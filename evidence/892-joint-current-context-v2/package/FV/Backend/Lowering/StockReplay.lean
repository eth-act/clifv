import FV.Backend.Lowering.Stock

/-!
Local replay of the stock driver's backward-scan transitions. Exact equality
checks all state, decision, results, rule ids and emitted instructions. This is
one component of the replacement certificate, not whole-function validation:
source contexts, schedule order, edges and output assembly remain separate.
-/

namespace Backend.Stock

def checkScan (ctx : Ctx) (block i ti : Nat) (isBranch : Bool) (input : State)
    (output : Scan) : Bool :=
  match scanInstruction ctx block i ti isBranch input with
  | .error _ => false
  | .ok actual => decide (actual = output)

def ScanEvent.check (event : ScanEvent) : Bool :=
  checkScan event.ctx event.block event.inst event.termInst event.isBranch event.input event.output

/-- Replay a supplied complete scan, checking the exact requested instruction
list and the state link between each pair of adjacent transitions. -/
def replayScans (check : Nat → State → Scan → Bool) :
    List Nat → State → List ScanRecord → Option (State × Array MInst)
  | [], input, [] => some (input, #[])
  | i :: indices, input, record :: records => do
    if record.inst != i || decide (record.input ≠ input) || !check i input record.output then
      none
    else
      let (final, code) ← replayScans check indices record.output.state records
      some (final, code ++ record.output.emitted)
  | _, _, _ => none

/-- Tail-recursive replay keeps stack usage independent of block length. -/
def replayScansAux (check : Nat → State → Scan → Bool) :
    List Nat → State → List ScanRecord → Array MInst → Option (State × Array MInst)
  | [], input, [], code => some (input, code)
  | i :: indices, input, record :: records, code =>
    if record.inst != i || decide (record.input ≠ input) || !check i input record.output then
      none
    else replayScansAux check indices record.output.state records (record.output.emitted ++ code)
  | _, _, _, _ => none

def replayScansTail (check : Nat → State → Scan → Bool) (indices : List Nat)
    (input : State) (records : List ScanRecord) : Option (State × Array MInst) :=
  replayScansAux check indices input records #[]

def checkScans (check : Nat → State → Scan → Bool) (indices : List Nat)
    (input : State) (output : BlockScan) : Bool :=
  decide (replayScansTail check indices input output.records = some (output.state, output.code))

def checkBlockScan (ctx : Ctx) (block ti : Nat) (isBranch : Bool) (indices : List Nat)
    (input : State) (output : BlockScan) : Bool :=
  checkScans (fun i => checkScan ctx block i ti isBranch) indices input output

/-- Canonical scan metadata from the source function in the supplied context.
Validating the context itself against the function remains a separate obligation. -/
structure ScanSource where
  termInst : Nat
  isBranch : Bool
  indices : List Nat
  deriving DecidableEq

def scanSource? (f : Clif.Function) (block : Nat) : Option ScanSource := do
  let b ← f.blocks[block]?
  let start := (f.blocks.take block).foldl (fun n b => n + b.body.length + 1) 0
  let ti := start + b.body.length
  let isBranch := match b.term with | .ret .. | .trap .. => false | _ => true
  some ⟨ti, isBranch, ((List.range (b.body.length + 1)).map (start + ·)).reverse⟩

def BlockScanEvent.check (event : BlockScanEvent) : Bool :=
  match scanSource? event.ctx.func event.block with
  | none => false
  | some source =>
    decide (source = ⟨event.termInst, event.isBranch, event.indices⟩) &&
      checkBlockScan event.ctx event.block event.termInst event.isBranch event.indices
        event.input event.output

end Backend.Stock
