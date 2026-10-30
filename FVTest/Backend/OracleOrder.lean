import FV.Backend.Lowering.Stock
import FV.Backend.Regalloc
import Lean
import FV.Backend.DeadCleanup

/-!
# regalloc2's input in Cranelift's vreg numbering (#551)

regalloc2's answer depends on the vreg numbers of its input, not only on the code: its bundles
are created in vreg order, and the probe offset into the register list of a bundle is the
bundle's index plus its first instruction (`ion/process.rs`). Cranelift numbers vregs as its
lowering allocates them (192 reserved numbers, the CLIF values in layout order, then the
temporaries of the backward instruction traversal, aliases resolved). The legacy lowering
numbers its temporaries forward, so regalloc2 picks other registers than in stock Cranelift
even on identical code.

This module is the untrusted oracle side only: when the Stock driver's code (`Stock.lower`,
Cranelift's traversal and numbering), after the same dead cleanup and `prepare`, gives
regalloc2 the same input as the prepared VCode `vcp` up to a renaming of vregs (`sameInput`:
the same control-flow graph; per instruction the same operands in the same order with the same
kinds, positions and constraints, the same clobbers and the same branch/return kind; the same
block parameters and branch arguments), `lean-regalloc` is given the Stock-numbered code
instead of `vcp`. regalloc2's answer names no vregs (per-operand allocations, edits at program
points, spill slots), so it is read back against `vcp` (`buildRFunc vcp`) and checked by
`checkAlloc` on `vcp`, exactly as before: nothing here is trusted.
-/

namespace Backend.OracleOrder

/-- Extend the renaming `m` (vreg of `a` ↦ vreg of `b`, with its inverse `inv`) by the
operands of `a` and `b`, position by position; `none` if they do not correspond. -/
def matchOps (m inv : Std.HashMap Nat Nat) (a b : Array Operand) :
    Option (Std.HashMap Nat Nat × Std.HashMap Nat Nat) := do
  if a.size != b.size then none
  let mut m := m
  let mut inv := inv
  for (x, y) in a.zip b do
    if x.cls != y.cls || x.kind != y.kind || x.pos != y.pos || x.con != y.con then none
    match m[x.vreg]?, inv[y.vreg]? with
    | some y', _ => if y' != y.vreg then none
    | none, some _ => none
    | none, none => m := m.insert x.vreg y.vreg; inv := inv.insert y.vreg x.vreg
  pure (m, inv)

def regOps (cls : Reg → Option (Nat × RegClass)) (rs : Array Reg) : Array Operand :=
  rs.filterMap fun r => (cls r).map fun (n, c) => ⟨n, c, .use, .early, .any⟩

/-- Is regalloc2's input for `b` (`vcodeJson b`) that for `a` with its vregs renamed
injectively? -/
def sameInput (a b : VCode) : Bool := Id.run do
  if a.blocks.size != b.blocks.size then return false
  match a.cfg, b.cfg with
  | .ok (sa, pa), .ok (sb, pb) => if sa != sb || pa != pb then return false
  | _, _ => return false
  let vr : Reg → Option (Nat × RegClass) := fun | .vreg n c => some (n, c) | _ => none
  let mut m : Std.HashMap Nat Nat := {}
  let mut inv : Std.HashMap Nat Nat := {}
  for (x, y) in a.blocks.zip b.blocks do
    if x.insts.size != y.insts.size then return false
    if x.params.size != y.params.size || x.branchArgs.size != y.branchArgs.size then return false
    match matchOps m inv (regOps vr x.params) (regOps vr y.params) with
    | none => return false
    | some (m', inv') => m := m'; inv := inv'
    match matchOps m inv (regOps vr x.branchArgs) (regOps vr y.branchArgs) with
    | none => return false
    | some (m', inv') => m := m'; inv := inv'
    for (i, j) in x.insts.zip y.insts do
      if i.isTerminator != j.isTerminator || i.isRet != j.isRet || i.clobbers != j.clobbers then
        return false
      match i.operands, j.operands with
      | .ok oi, .ok oj =>
        match matchOps m inv oi oj with
        | none => return false
        | some (m', inv') => m := m'; inv := inv'
      | _, _ => return false
  let cls (v : VCode) (n : Nat) : Option RegClass := v.classes[n]?
  pure <| m.toList.all fun (n, n') => cls a n == cls b n'

/-- Diagnostics (`FV_RA_DIAG`): the first instruction where `a` and `b` differ with their vregs
erased (`none`: no such instruction, the difference is in the vreg structure). -/
def firstDiff (a b : VCode) : String := Id.run do
  let erase : Reg → Reg := fun | .vreg _ c => .vreg 0 c | r => r
  let flat (v : VCode) : Array MInst := v.blocks.foldl (fun acc x => acc ++ x.insts) #[]
  let (fa, fb) := (flat a, flat b)
  let sh (i : MInst) : String := String.ofList (((repr (i.mapRegs erase)).pretty 1000).toList.take 90)
  for k in [0:max fa.size fb.size] do
    let x := fa[k]?.map (·.mapRegs erase)
    let y := fb[k]?.map (·.mapRegs erase)
    if x != y then
      return s!"inst {k}/{fa.size}/{fb.size}: ours {(fa[k]?.map sh).getD "-"} | stock {(fb[k]?.map sh).getD "-"}"
  return s!"same shape (blocks {a.blocks.size}/{b.blocks.size}): vreg structure"

/-- The code given to `lean-regalloc` for the prepared `vcp` of `f` (`deadCleanup`: the
allocator's input was pruned): the Stock driver's prepared code if it is `vcp` renamed,
else `vcp`; with the reason (`"stock"`, or why `vcp` is kept). -/
def oracleCodeWhy (f : Option Clif.Function) (deadCleanup : Bool) (vcp : VCode) :
    VCode × String :=
  match f with
  | none => (vcp, "no CLIF function")
  | some f =>
    match Stock.lower f with
    | .error e => (vcp, s!"Stock.lower: {e}")
    | .ok r =>
      let vc := { r.code with name := vcp.name }
      let vc := if deadCleanup then DeadCleanup.prune vc else vc
      match prepare vc with
      | .ok s => if sameInput vcp s then (s, "stock") else (vcp, s!"different code: {firstDiff vcp s}")
      | .error e => (vcp, s!"prepare: {e}")

def oracleCode (f : Option Clif.Function) (deadCleanup : Bool) (vcp : VCode) : VCode :=
  (oracleCodeWhy f deadCleanup vcp).1

/-- `runLeanRegalloc` on the prepared `vcs`, giving `lean-regalloc` the code `oracle vcp` of
each (`oracleCode`); the answers are rebuilt against `vcp` itself. -/
def runLeanRegallocVia (bin : String) (env : MachineEnv) (oracle : VCode → VCode)
    (vcs : Array VCode) : IO (Except String (Array (Except String RAResult))) := do
  if vcs.isEmpty then return .ok #[]
  let mut funcs : Array String := #[]
  for vc in vcs do
    match vcodeJson (oracle vc) with
    | .ok j => funcs := funcs.push j
    | .error e => return .error s!"%{vc.name}: {e}"
  let input := s!"\{\"env\":{envJson env},\"functions\":[" ++ ",".intercalate funcs.toList ++ "]}\n"
  let (h, path) ← IO.FS.createTempFile
  h.putStr input
  h.flush
  if let some keep ← IO.getEnv "LEAN_REGALLOC_KEEP" then IO.FS.writeFile keep input
  let out ← IO.Process.output { cmd := bin, args := #[path.toString] }
  IO.FS.removeFile path
  if out.exitCode != 0 then
    return .error s!"lean-regalloc ({bin}) failed with status {out.exitCode}: {out.stderr}"
  match Lean.Json.parse out.stdout with
  | .error e => return .error s!"lean-regalloc output: {e}"
  | .ok j =>
    let arr := ((j.getObjVal? "functions").bind (·.getArr?)).toOption.getD #[]
    if arr.size != vcs.size then return .error "lean-regalloc: function count differs"
    return .ok <| (vcs.zip arr).map fun (vc, fj) => do
      let o ← parseRAOut fj
      let rf ← buildRFunc vc o
      pure { prepared := vc, rf, rustChecker := o.checker }

end Backend.OracleOrder
