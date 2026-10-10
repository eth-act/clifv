import FV.Backend.RegallocOps
import Std.Data.HashSet

/-! Measurement-only prototype. Not enabled by the production compiler and not
covered by its theorems. Do not promote this module before the comparison gate
and the required semantic/structural proofs have passed. -/

namespace Backend.DeadCleanupPrototype

private def pureAlu : ALUOp → Bool
  | .add | .sub | .orr | .orrNot | .and | .andNot | .eor | .eorNot => true
  | _ => false

/-- An explicit whitelist: no flags, loads, stores, calls, traps or control flow. -/
def removable : MInst → Bool
  | .mov .. | .movWide .. | .loadAddr .. => true
  | .aluRRR op .. | .aluRRImm12 op .. | .aluRRImmLogic op ..
  | .aluRRImmShift op .. | .aluRRRShift op .. | .aluRRRExtend op .. => pureAlu op
  | .aluRRRR .mAdd .. | .aluRRRR .mSub .. => true
  | _ => false

private def addRegs (s : Std.HashSet Nat) (rs : Array Reg) : Std.HashSet Nat :=
  rs.foldl (fun s r => match r with | .vreg n _ => s.insert n | _ => s) s

private def addUses (s : Std.HashSet Nat) (m : MInst) (nregs : Nat) : Std.HashSet Nat :=
  match m.operands with
  | .ok ops => ops.foldl (fun s op => if op.kind == .use then s.insert op.vreg else s) s
  -- Unknown operands cannot justify deletion of any producer.
  | .error _ => (List.range nregs).foldl (·.insert ·) s

private def blockUses (s : Std.HashSet Nat) (b : VBlock) (nregs : Nat) : Std.HashSet Nat :=
  b.insts.foldl (fun s m => addUses s m nregs) (addRegs s b.branchArgs)

private def cleanBlock (vc : VCode) (idx : Nat) (b : VBlock) : VBlock := Id.run do
  let mut live : Std.HashSet Nat := addRegs {} b.branchArgs
  for (other, j) in vc.blocks.zipIdx do
    if j != idx then
      live := blockUses live other vc.classes.size
  let mut kept : List MInst := []
  for m in b.insts.toList.reverse do
    let dead := !m.defs.isEmpty && m.defs.all fun r => match r with
      | .vreg n _ => !live.contains n
      | _ => false
    if !(removable m && m.clobbers.isEmpty && dead) then
      match m.operands with
      | .ok ops =>
        for op in ops do
          if op.kind == .def then live := live.erase op.vreg
      | .error _ => pure ()
      live := addUses live m vc.classes.size
      kept := m :: kept
  return { b with insts := kept.toArray }

/-- Pure filtering; numbering, metadata and edges remain unchanged. -/
def clean (vc : VCode) : VCode :=
  { vc with blocks := vc.blocks.mapIdx (fun idx b => cleanBlock vc idx b) }

end Backend.DeadCleanupPrototype
