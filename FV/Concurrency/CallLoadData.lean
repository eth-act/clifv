import FV.Concurrency.CallSeg
import FV.Concurrency.CallThreadWitness

/-!
# A compiled caller of the compiled `atomic_load`: data and checks (T2h, #311, calls)

The CLIF `%f(i64) -> i64 { fn0 = colocated %ld(i64) -> i64; v1 = call fn0(v0); return v1 }`
(`fC`) as the pipeline compiles it: the prologue, the 18 saves, the entry `args`, the spill of
`x0` and back, then `bl ld` (a direct call, no GOT pair). Its activation `RC` runs at `0x30000`
with `sp = 0x7000`, the compiled `atomic_load` (`RealizeCompiled.WitnessL.RAL`'s code at
`0x20000`, as `act` lays it out) in memory too (kept addresses `GL`); its call hook enters that code (`enterL`: the
callee's program, pc at its base, x30 the return address).

Checks by `native_decide` (witness only).
-/

namespace Concurrency.CallSeg.WitnessC

open Arm ArmFoot ArmThread Prog ClifThread ProgE2E Backend Backend.Proof Backend.Proof.Driver
  VCodeThread PrepThread AllocThread ThreadRefine ArmAllocThread E2E ArmInstFoot Code
  RealizeCompiled RealizeCompiled.Witness RealizeCompiled.WitnessL
open ArmAllocThread.Witness (act entryAt codeMem)

/-- The caller. -/
def srcC : String := "function %f(i64) -> i64 {
    fn0 = colocated %ld(i64) -> i64

block0(v0: i64):
    v1 = call fn0(v0)
    return v1
}
"

def fC : Clif.Function :=
  match Clif.parse srcC with
  | .ok p => p.funcs.headD default
  | .error _ => default

def vcC : VCode := match lowerFunction fC with
  | .ok vc => vc
  | .error _ => default

def vcpC : VCode := match Backend.prepare vcC with
  | .ok vcp => vcp
  | .error _ => default

def rfC : RFunc := spillAlloc vcpC

/-- The callee's program (the compiled `atomic_load` at `0x20000`). -/
abbrev pL : Arm.Program := (act vcpL rfL).fb.program 0x20000#64

/-- **Enter the compiled `atomic_load`**: its program, the pc at its base, x30 the return
address. -/
def enterL (s : ArmState) : ArmState :=
  w .PC 0x20000#64 (w (.GPR 30#5) (r .PC s + 4#64) (set_program s pL))

/-- The callee's code addresses. -/
def GL (a : BitVec 64) : Prop := (a - 0x20000#64).toNat < 4 * (act vcpL rfL).fb.words.size

instance (a : BitVec 64) : Decidable (GL a) := by unfold GL; infer_instance

/-- Both functions' code in memory. -/
def memC : Memory := fun a =>
  if GL a then RAL.s0.mem a else codeMem (act vcpC rfC).fb 0x30000#64 a

/-- The caller's ABI entry state: sp `0x7000`, its code at `0x30000`, the callee's in memory. -/
def sC0 : ArmState := setMem memC (entryAt 0x7000#64 (act vcpC rfC).fb 0x30000#64)

/-- The call hook: `bl ld` enters the compiled `atomic_load`. -/
def HC : ArmHooks := ⟨fun d s => if d = some "ld" then enterL s else s, fun _ _ s => s⟩

/-- **The caller's activation** (module doc). -/
def RC : RL := { act vcpC rfC with base := 0x30000#64, s0 := sC0, H := HC, G := GL }

theorem factsC : (checkAlloc vcpC rfC).isOk = true ∧ (lowerRFunc vcpC rfC).toBool = true ∧
    (emitFunc 0 (act vcpC rfC).af).toBool = true ∧ (act vcpC rfC).fa.k = 0 ∧
    (act vcpC rfC).fa.layout.toBool = true ∧
    (labelOffsets (act vcpC rfC).fa.lines).toBool = true ∧
    4 * (act vcpC rfC).fb.words.size ≤ 2 ^ 64 ∧ (act vcpC rfC).af.frameSize ≤ 0x100 ∧
    4 * (act vcpC rfC).fb.words.size ≤ 0x10000 ∧
    (blocksLinesE (act vcpC rfC).ctx (act vcpC rfC).af (act vcpC rfC).af.blocks.toList {}).toBool =
      true := by
  native_decide

theorem allocC : checkAlloc vcpC rfC = .ok () := by
  have h := factsC.1
  revert h
  cases checkAlloc vcpC rfC with
  | ok u => intro _; rfl
  | error e => intro h; cases h

theorem codeRC : ∀ k < RC.fb.words.size,
    Arm.read_mem_bytes 4 (0x30000#64 + BitVec.ofNat 64 (4 * k)) RC.s0 = RC.fb.words[k]! := by
  native_decide

/-- The entry `args` of the caller reads argument registers only. -/
theorem entryArgRC : ∀ r, RC.vc.EntryArg r → r.isArgReg = true := by
  rintro r ⟨vb, ds, h1, h2, v, hv⟩
  have h : entryArgsB vcpC = true := by native_decide
  simp only [entryArgsB, show vcpC = RC.vc from rfl, h1, h2, List.all_eq_true] at h
  exact h _ hv

/-- The items after the spill moves. -/
def restC : List RItem := (rfC.blocks[0]!).toList.drop 21

/-- The code of the items after the spill moves starts with the call of `ld` (as a check). -/
def headBlB : Bool :=
  match itemsCode RC.fr vcpC.blocks[0]! restC with
  | .ok (.inst (.call ⟨.sym "ld", _, _⟩) :: _) => true
  | _ => false

/-- The entry `args` (as a check). -/
def argsBC : Bool :=
  match vcpC.blocks[0]? with
  | some vb => (match vb.insts[0]? with
    | some (MInst.args [(Reg.vreg 0 RegClass.int, Reg.x 0)]) => true
    | _ => false) && vb.insts.size == 3
  | none => false

theorem checksRunC : (rfC.blocks[0]!).toList = savesL.map (fun p => RItem.move p.1 p.2) ++
      (.op 0 #[.reg (.x 0)] :: (spillL.map (fun p => RItem.move p.1 p.2) ++ restC)) ∧
    headBlB = true ∧ argsBC = true ∧ 0 < vcpC.blocks.size := by
  native_decide

theorem progC_min : (RC.fb.program RC.base).min? ≠ pL.min? := by native_decide

theorem progC_ne : RC.fb.program RC.base ≠ pL := fun h => progC_min (by rw [h])

theorem x0C : regVal RC.s0 (.x 0) = 0 := by native_decide

theorem spC : E2E.spv RC.s0 = 0x7000#64 ∧ frameDrop RC.af = 240 ∧
    frameDrop (act vcpL rfL).af = 240 ∧ (act vcpL rfL).fb.words.size ≤ 0x4000 ∧
    RC.fb.words.size ≤ 0x4000 ∧ RC.fr.size ≤ 240 ∧ (act vcpL rfL).fr.size ≤ 240 ∧
    RC.af.frameSize = 224 ∧ (act vcpL rfL).af.frameSize = 224 := by
  native_decide

end Concurrency.CallSeg.WitnessC
