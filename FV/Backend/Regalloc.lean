import FV.Backend.RegallocCheck
import Lean.Data.Json
import FV.Backend.Proof.PrepareCheck

/-!
# regalloc2 as the backend's register allocator (M6)

`allocateRegalloc2 bin env vcs` allocates a batch of functions (one `.clif` file) with the
external, untrusted `lean-regalloc` (`rust/crates/lean-regalloc`, regalloc2 0.15.2 with
Cranelift 0.136.1's options):

1. `prepare` each `VCode` (drop unreachable blocks, split critical edges);
2. write the functions as JSON (`vcodeJson`; schema in `docs/contracts/regalloc.md`) with the
   machine environment `aarch64Env`, run `lean-regalloc IN.json` (`IO.Process.output`), parse
   its JSON answer;
3. build the allocated function `RFunc` (`buildRFunc`): per block, the original instructions
   with their operand locations and regalloc2's edits (moves, spills, reloads) at their
   program points, plus a save of every callee-saved register the allocation touches at the
   entry and a restore before every return;
4. **check** it (`checkAlloc`, `FV/Backend/RegallocCheck.lean`; a rejection is a compile
   error, as is a rejection by regalloc2's own checker, which runs as an extra cross-check);
5. lay out the frame and lower to `AFunc` (`lowerRFunc`): substitute the registers
   (`MInst.assign`), turn moves into `mov`/`str`/`ldr`, drop `Args`, turn `Rets` into the
   epilogue.

Frame (grows down; `sp` is 16-byte aligned everywhere; all offsets are from `sp`). The
allocator's slots sit right above the outgoing area, below the explicit CLIF slots, so their
offsets stay small (`size < 32 KiB`, checked by `lowerRFunc`) however large the CLIF slots are:

```
fp + 16 + off     incoming stack arguments
fp + 8, fp        saved lr, fp                                  <- x29
                  padding to 16                                 (total = frameSize)
sp + size         explicit CLIF stack slots (slotBase)
sp + fmoveTmp     16-byte temporary for float register moves (if any)
sp + saveBase     callee-save slots: float registers (16 bytes each), then int (8 bytes)
sp + floatBase    float spill slots, 16 bytes each (if any float value is spilled)
sp + intBase      int spill slots, 8 bytes each
sp                outgoing stack arguments                       <- sp
```
-/

namespace Backend

open Lean (Json)

/-! ## VCode → JSON -/

def jstr (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '"' then "\\\"" else if c == '\\' then "\\\\"
    else if c.toNat < 0x20 then " " else c.toString) ++ "\""

def Reg.pregName : Reg → String
  | .x n => s!"x{n}"
  | .v n => s!"v{n}"
  | r => s!"<{repr r}>"

def jlist (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"

/-- `aarch64Env` in the schema of `lean-regalloc` (classes int, float, vector). -/
def envJson (e : MachineEnv) : String :=
  let regs (rs : List Reg) := jlist (rs.map fun r => jstr r.pregName)
  s!"\{\"preferred\":[{regs e.preferredInt},{regs e.preferredFloat},[]]," ++
  s!"\"non_preferred\":[{regs e.nonPreferredInt},{regs e.nonPreferredFloat},[]]," ++
  "\"scratch\":[null,null,null],\"fixed_stack\":[]}"

def Operand.json (o : Operand) : String :=
  let k := match o.kind with | .use => "use" | .def => "def"
  let p := match o.pos with | .early => "early" | .late => "late"
  let c := match o.con with
    | .any => "any" | .reg => "reg" | .stack => "stack"
    | .fixed r => s!"fixed:{r.pregName}" | .reuse i => s!"reuse:{i}"
  s!"\{\"v\":{o.vreg},\"k\":\"{k}\",\"p\":\"{p}\",\"c\":\"{c}\"}"

/-- One prepared function as `lean-regalloc` input. -/
def vcodeJson (vc : VCode) : Except String String := do
  let (succs, preds) ← vc.cfg
  let classes := String.ofList (vc.classes.toList.map fun | .int => 'i' | .float => 'f')
  let mut start := 0
  let mut blocks : Array String := #[]
  let mut insts : Array String := #[]
  for (b, bi) in vc.blocks.zipIdx do
    let params ← b.params.toList.mapM vregNum
    blocks := blocks.push <| s!"\{\"insts\":[{start},{start + b.insts.size}]," ++
      s!"\"succs\":{jlist (succs[bi]!.toList.map toString)}," ++
      s!"\"preds\":{jlist (preds[bi]!.toList.map toString)}," ++
      s!"\"params\":{jlist (params.map toString)}}"
    start := start + b.insts.size
    for (i, k) in b.insts.zipIdx do
      let ops ← i.operands
      let last := k + 1 == b.insts.size
      let kind := if i.isRet then "ret" else if i.isBranch then "branch" else "other"
      if last != (i.isRet || i.isBranch) then
        throw s!"block {b.label}: terminator not at the end of the block"
      let args ← if i.isBranch then do
          let xs ← b.branchArgs.toList.mapM vregNum
          let per := succs[bi]!.toList.map fun _ => jlist (xs.map toString)
          pure s!",\"args\":{jlist per}"
        else pure ""
      let clob := jlist (i.clobbers.map fun r => jstr r.pregName)
      insts := insts.push <| s!"\{\"ops\":{jlist (ops.toList.map Operand.json)}," ++
        s!"\"clobbers\":{clob},\"kind\":\"{kind}\"{args}}"
  pure <| s!"\{\"name\":{jstr vc.name},\"entry\":0,\"vregs\":\"{classes}\"," ++
    s!"\"blocks\":{jlist blocks.toList},\"insts\":{jlist insts.toList}}"

/-! ## regalloc2's answer → `RFunc` -/

/-- regalloc2's answer for one function. -/
structure RAOut where
  allocs : Array (Array String)
  /-- `(inst, after?, from, to)` in program-point order. -/
  edits : Array (Nat × Bool × String × String)
  spillSlots : Nat
  /-- Verdict of regalloc2's own checker (`"ok"` or its errors). -/
  checker : String
  deriving Inhabited

def parseRAOut (j : Json) : Except String RAOut := do
  if !((j.getObjValAs? Bool "ok").toOption.getD false) then
    throw s!"regalloc2: {(j.getObjValAs? String "error").toOption.getD "failed"}"
  let allocs ← (← j.getObjValAs? (Array (Array String)) "allocs") |> pure
  let edits ← (← (← j.getObjVal? "edits").getArr?).mapM fun e => do
    let pos ← e.getObjValAs? String "pos"
    pure (← e.getObjValAs? Nat "inst", pos == "after",
          ← e.getObjValAs? String "from", ← e.getObjValAs? String "to")
  pure { allocs, edits, spillSlots := ← j.getObjValAs? Nat "num_spillslots",
         checker := ← j.getObjValAs? String "checker" }

def parseRealReg (s : String) : Option Reg :=
  let n? := (s.drop 1).toString.toNat?
  if s.startsWith "x" then n?.map .x
  else if s.startsWith "v" then n?.map .v
  else none

/-- An allocation string of an operand of class `cls`: `x3`, `v8`, `s2` (spill slot). -/
def parseLoc (s : String) (cls : RegClass) : Except String Loc :=
  if s.startsWith "s" then
    match (s.drop 1).toString.toNat? with
    | some n => pure (.stack n cls)
    | none => throw s!"bad allocation {s}"
  else match parseRealReg s with
    | some r => pure (.reg r)
    | none => throw s!"bad allocation {s}"

/-- A regalloc2 edit `from → to`; the class is the register side's (never stack to stack). -/
def parseMove (src dst : String) : Except String RItem := do
  let cls ← match parseRealReg src, parseRealReg dst with
    | some r, _ | none, some r => match r.realClass? with
      | some c => pure c
      | none => throw s!"bad register in move {src} → {dst}"
    | none, none => throw s!"stack-to-stack move {src} → {dst}"
  pure (.move (← parseLoc src cls) (← parseLoc dst cls))

def RItem.locs : RItem → List Loc
  | .op _ ls => ls.toList
  | .move a b => [a, b]

/-- The allocated function: regalloc2's allocations and edits in program order, plus
callee-saved saves at the entry and restores before every `Rets`. -/
def buildRFunc (vc : VCode) (o : RAOut) : Except String RFunc := do
  let ninsts := vc.blocks.foldl (fun n b => n + b.insts.size) 0
  if o.allocs.size != ninsts then throw "regalloc2: allocation count differs"
  let mut before : Array (Array RItem) := Array.replicate ninsts #[]
  let mut after : Array (Array RItem) := Array.replicate ninsts #[]
  for (g, isAfter, src, dst) in o.edits do
    if g ≥ ninsts then throw "regalloc2: edit at a missing instruction"
    let m ← parseMove src dst
    if isAfter then after := after.modify g (·.push m) else before := before.modify g (·.push m)
  let mut g := 0
  let mut blocks : Array (Array RItem) := #[]
  for b in vc.blocks do
    let mut items : Array RItem := #[]
    for (i, k) in b.insts.zipIdx do
      let ops ← i.operands
      let strs := o.allocs[g]!
      if strs.size != ops.size then throw s!"regalloc2: allocation count of block {b.label} inst {k}"
      let locs ← (ops.zip strs).mapM fun (op, s) => parseLoc s op.cls
      items := items ++ before[g]! |>.push (.op k locs) |>.append after[g]!
      g := g + 1
    blocks := blocks.push items
  let used := blocks.foldl (fun acc items => items.foldl (fun acc it => acc ++ it.locs) acc) []
  let saved := calleeSaved.filter fun r => used.contains (.reg r)
  let saves : Array RItem := saved.toArray.map fun r => .move (.reg r) (.save r)
  let restores : Array RItem := saved.toArray.map fun r => .move (.save r) (.reg r)
  let blocks' := blocks.mapIdx fun bi items =>
    let vb := vc.blocks[bi]!
    let items := items.flatMap fun it => match it with
      | .op k _ => if vb.insts[k]! matches .rets _ then restores.push it else #[it]
      | _ => #[it]
    if bi == 0 then saves ++ items else items
  pure { blocks := blocks', spillSlots := o.spillSlots, saved }

/-! ## Frame and lowering to `AFunc` -/

structure RAFrame where
  intBase : Nat
  floatBase : Nat
  saveOff : List (Reg × Nat)
  fmoveTmp : Nat
  /-- End of the allocator's slots (16-aligned); the explicit CLIF slots start here. -/
  size : Nat
  /-- The whole frame below fp/lr: allocator slots and CLIF slots (`AFunc.frameSize`). -/
  total : Nat
  deriving Repr, Inhabited

/-- Does the allocated code use a float spill slot? -/
def RFunc.floatStack (rf : RFunc) : Bool :=
  (rf.blocks.foldl (· ++ ·) #[]).any fun it => it.locs.any fun | .stack _ .float => true | _ => false

/-- Does the allocated code move between float registers (needs `fmoveTmp`)? -/
def RFunc.floatMove (rf : RFunc) : Bool :=
  (rf.blocks.foldl (· ++ ·) #[]).any fun
    | .move (.reg (.v _)) (.reg (.v _)) => true
    | _ => false

def RAFrame.compute (vc : VCode) (rf : RFunc) : RAFrame :=
  let floatStack := rf.floatStack
  let floatMove := rf.floatMove
  let intBase := alignTo vc.outgoing 16
  let floatBase := alignTo (intBase + 8 * rf.spillSlots) 16
  let saveBase := floatBase + (if floatStack then 16 * rf.spillSlots else 0)
  let floats := rf.saved.filter (·.realClass? == some .float)
  let ints := rf.saved.filter (·.realClass? == some .int)
  let (fo, e) := floats.foldl (fun (acc, o) r => (acc ++ [(r, o)], o + 16)) ([], saveBase)
  let (io, e) := ints.foldl (fun (acc, o) r => (acc ++ [(r, o)], o + 8)) ([], e)
  let tmp := alignTo e 16
  let e := if floatMove then tmp + 16 else e
  let size := alignTo e 16
  { intBase, floatBase, saveOff := fo ++ io, fmoveTmp := tmp, size,
    total := alignTo (size + vc.slotBytes) 16 }

def RAFrame.offset (fr : RAFrame) : Loc → Except String Nat
  | .stack s .int => pure (fr.intBase + 8 * s)
  | .stack s .float => pure (fr.floatBase + 16 * s)
  | .save r => match fr.saveOff.lookup r with
    | some o => pure o
    | none => throw s!"no save slot for {repr r}"
  | l => throw s!"{repr l} is not a frame slot"

/-- Machine code of a move. -/
def RAFrame.moveInsts (fr : RAFrame) (src dst : Loc) : Except String (List AInst) := do
  match src, dst with
  | .reg a, .reg b => match a.realClass? with
    | some .int => pure [.inst (.mov .size64 b a)]
    | _ => pure [.inst (slotStore .float a fr.fmoveTmp), .inst (slotLoad .float b fr.fmoveTmp)]
  | .reg a, m => pure [.inst (slotStore ((a.realClass?).getD .int) a (← fr.offset m))]
  | m, .reg b => pure [.inst (slotLoad ((b.realClass?).getD .int) b (← fr.offset m))]
  | _, _ => throw "memory-to-memory move"

/-- Lower a checked allocated function to `AFunc`. -/
def lowerRFunc (vc : VCode) (rf : RFunc) : Except String AFunc := do
  let fr := RAFrame.compute vc rf
  -- Allocator slots are addressed `[sp, #off]` (`ldur`/`stur` or scaled `ldr`/`str`); the model
  -- has no SIMD&FP register-offset form, so an allocator area of 32 KiB or more is rejected
  -- (proof: `RegallocSlots`). The CLIF slots above it are addressed by `stack_addr` arithmetic.
  if fr.size ≥ 32768 then throw s!"allocator frame area of {fr.size} bytes is too large"
  let blocks ← (vc.blocks.zip rf.blocks).mapIdxM fun bi (vb, items) => do
    let mut code : Array AInst := if bi == 0 then #[.prologue] else #[]
    for it in items do
      match it with
      | .move src dst => code := code ++ (← fr.moveInsts src dst).toArray
      | .op k allocs =>
        let regs ← allocs.mapM fun | .reg r => pure r | l => throw s!"operand in {repr l}"
        let some i := vb.insts[k]? | throw "missing instruction"
        match ← i.assign regs with
        | .args _ => pure ()
        | .rets _ => code := code.push .epilogueRet
        | m => code := code.push (.inst m)
    pure (vb.label, code)
  -- A leaf function with an empty frame that never addresses `fp` needs no frame (x29/x30
  -- are neither written nor read).
  let usesFp := vc.blocks.any fun b => b.insts.any fun
    | .load _ _ (.fpOffset _) _ | .store _ _ (.fpOffset _) _ | .loadAddr _ (.fpOffset _) => true
    | _ => false
  let calls := vc.blocks.any fun b => b.insts.any fun | .call _ => true | _ => false
  let frame := fr.total != 0 || calls || usesFp
  pure { name := vc.name, frameSize := fr.total, blocks, slotBase := fr.size, frame }

/-! ## The allocator -/

/-- Everything about one allocated function (for tests: `RFunc` can be mutated and rechecked). -/
structure RAResult where
  prepared : VCode
  rf : RFunc
  /-- regalloc2's own checker verdict. -/
  rustChecker : String
  deriving Inhabited

/-- Check, then lower. A rejection by either checker is an error. -/
def RAResult.finish (r : RAResult) : Except String AFunc := do
  match checkAlloc r.prepared r.rf with
  | .ok () => pure ()
  | .error e => throw s!"register allocation rejected by the Lean checker: {e}"
  if r.rustChecker != "ok" then
    throw s!"register allocation rejected by regalloc2's checker: {r.rustChecker}"
  lowerRFunc r.prepared r.rf

/-- Run `lean-regalloc` on prepared functions. -/
def runLeanRegalloc (bin : String) (env : MachineEnv) (vcs : Array VCode) : IO (Except String (Array (Except String RAResult))) := do
  if vcs.isEmpty then return .ok #[]
  let mut funcs : Array String := #[]
  for vc in vcs do
    match vcodeJson vc with
    | .ok j => funcs := funcs.push j
    | .error e => return .error s!"%{vc.name}: {e}"
  let input := s!"\{\"env\":{envJson env},\"functions\":[" ++ ",".intercalate funcs.toList ++ "]}\n"
  let (h, path) ← IO.FS.createTempFile
  h.putStr input
  h.flush
  -- debugging aid: keep a copy of the allocator input
  if let some keep ← IO.getEnv "LEAN_REGALLOC_KEEP" then IO.FS.writeFile keep input
  let out ← IO.Process.output { cmd := bin, args := #[path.toString] }
  IO.FS.removeFile path
  if out.exitCode != 0 then
    return .error s!"lean-regalloc ({bin}) failed with status {out.exitCode}: {out.stderr}"
  match Json.parse out.stdout with
  | .error e => return .error s!"lean-regalloc output: {e}"
  | .ok j =>
    let arr := ((j.getObjVal? "functions").bind (·.getArr?)).toOption.getD #[]
    if arr.size != vcs.size then return .error "lean-regalloc: function count differs"
    return .ok <| (vcs.zip arr).map fun (vc, fj) => do
      let o ← parseRAOut fj
      let rf ← buildRFunc vc o
      pure { prepared := vc, rf, rustChecker := o.checker }

/-- Allocate a batch of functions with regalloc2 (one `lean-regalloc` run); every result is
checked by `checkAlloc`. -/
def allocateRegalloc2 (bin : String) (env : MachineEnv) (vcs : Array VCode) : IO (Array (Except String AFunc)) := do
  -- `prepare`, then M7's `prepare` validator (`prepCheck`, assumed by the end-to-end theorem)
  let prepared := vcs.map fun vc => do
    let vcp ← prepare vc
    if !Proof.Driver.prepCheck vc vcp then
      throw "prepare rejected by the M7 prepare validator (prepCheck)"
    pure vcp
  let ok := prepared.filterMap (·.toOption)
  match ← runLeanRegalloc bin env ok with
  | .error e => pure (vcs.map fun _ => .error e)
  | .ok rs =>
    let mut out : Array (Except String AFunc) := #[]
    let mut j := 0
    for p in prepared do
      match p with
      | .error e => out := out.push (.error e)
      | .ok _ =>
        out := out.push (rs[j]!.bind RAResult.finish)
        j := j + 1
    pure out

end Backend
