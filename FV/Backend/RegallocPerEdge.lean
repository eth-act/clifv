import FV.Backend.RegallocCheck

/-! Per-successor register-allocation checker. Existing checkAlloc and all its
consumers remain unchanged until the new full simulation is established. -/
namespace Backend
section
variable (c : CheckCtx)

/-- Check the selected outgoing vector, then update symbolic value aliases. -/
def CheckCtx.edgeCopyAt (edges : Array (Array (Array Reg))) (b s index : Nat) (a : AState) :
    Except String AState :=
  match c.vc.blocks[b]?,c.vc.blocks[s]? with
  | some vb,some sb => do
    let some args := edges[b]?.bind (·[index]?) | throw s!"edge {b}/{index}: missing arguments"
    ensure (args.size == sb.params.size) fun _ =>
      s!"edge {vb.label} → {sb.label}: {args.size} arguments for {sb.params.size} parameters"
    if args.isEmpty then pure a
    else do
      let ps ← sb.params.toList.mapM vregNum
      let xs ← args.toList.mapM vregNum
      ensure (decide ps.Nodup) fun _ => s!"block {sb.label}: parameters are not distinct"
      pure (a.parCopy ps xs)
  | none,_ => throw s!"no block {b}"
  | _,none => throw s!"no block {s}"

/-- Existing conservative dead-def forgetting, followed by the selected copy. -/
def CheckCtx.edgeAt (edges : Array (Array (Array Reg))) (b s index : Nat) (a : AState) :
    Except String AState :=
  c.edgeCopyAt edges b s index (c.edgeForget b s a)

def CheckCtx.roundAt (edges : Array (Array (Array Reg))) (ins : Array (Option AState)) : Except String (Array (Option AState) × Bool) := do
  let mut ins := ins
  let mut changed := false
  for b in [0:c.vc.blocks.size] do
    let some a := ins[b]! | continue
    let out ← c.runBlock b a
    for (s, index) in c.succs[b]!.zipIdx.toList do
      let e ← c.edgeAt edges b s index out
      let new := match ins[s]! with
        | none => e
        | some old => old.meet e
      if ins[s]! != some new then
        ins := ins.set! s (some new)
        changed := true
  pure (ins, changed)

/-- The (untrusted) fixpoint iteration: it only proposes in-states; `verify` checks them. -/
def CheckCtx.fixpointAt (edges : Array (Array (Array Reg))) (fuel : Nat) (ins : Array (Option AState)) :
    Except String (Array (Option AState)) :=
  match fuel with
  | 0 => throw "checker did not reach a fixpoint (fuel exhausted)"
  | fuel + 1 => do
    let (ins, changed) ← c.roundAt edges ins
    if changed then CheckCtx.fixpointAt edges fuel ins else pure ins

/-- Block `b` of the proposed in-states `ins`: reached, its items check from its in-state, and
every successor's in-state is included in the state the edge produces. -/
def CheckCtx.verifyBlockAt (edges : Array (Array (Array Reg))) (ins : Array (Option AState)) (b : Nat) : Except String Unit :=
  match ins[b]? with
  | some (some a) => do
    let out ← c.runBlock b a
    (c.succs[b]?.getD #[]).zipIdx.toList.forM fun (s,index) => do
      let e ← c.edgeAt edges b s index out
      match ins[s]? with
      | some (some a') => ensure (a'.le e) fun _ => s!"block {s}: in-state is not a fixpoint"
      | _ => throw s!"block {s} is never reached"
  | _ => throw s!"block {b} is never reached"

end

/-- Check the proposed in-states: the entry block's is included in `entryState`, every block
passes `verifyBlock`. This (not the iteration) is what the soundness proof relies on. -/
def CheckCtx.verifyAt (c : CheckCtx) (edges : Array (Array (Array Reg))) (ins : Array (Option AState)) : Except String Unit :=
  match ins[0]? with
  | some (some a0) => do
    ensure (a0.le (entryState c.size)) fun _ => "entry in-state is not the entry state"
    (List.range c.vc.blocks.size).forM (c.verifyBlockAt edges ins)
  | _ => throw "the entry block is never reached"

/-- Check an allocated function against the (prepared) VCode it was allocated from. -/
def checkAllocAt (vc : VCode) (edges : Array (Array (Array Reg))) (rf : RFunc) : Except String Unit := do
  let (succs, preds) ← vc.cfg
  ensure (vc.blocks.size != 0) fun _ => "no blocks"
  ensure (rf.blocks.size == vc.blocks.size) fun _ => "block count differs"
  ensure (preds[0]!).isEmpty fun _ => "the entry block is a branch target"
  ensure (vc.blocks[0]!).params.isEmpty fun _ => "the entry block has parameters"
  ensure (rf.saved.all calleeSaved.contains) fun _ =>
    "save slot for a register that is not callee-saved"
  -- every instruction has an operand view
  let _ ← vc.blocks.mapM fun b => b.insts.mapM MInst.operands
  let size := 128 + 2 * rf.spillSlots
  let c : CheckCtx := { vc, succs, rf, size }
  let nsyms := vc.classes.size + calleeSaved.length
  let fuel := vc.blocks.size * (size * nsyms + 1) + 2
  let ins0 := (Array.replicate vc.blocks.size none).set! 0 (some (entryState size))
  let ins ← c.fixpointAt edges fuel ins0
  ins.zipIdx.toList.forM fun (s, b) =>
    ensure s.isSome fun _ => s!"block {(vc.blocks[b]!).label} is never reached"
  c.verifyAt edges ins

end Backend
