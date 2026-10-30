import FV.Concurrency.RealizeWitnessLoad

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
    (emitPlan (act vcpC rfC).fa.k (act vcpC rfC).af).toBool = true := by
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

theorem spC : E2E.spv RC.s0 = 0x7000#64 ∧ frameDrop RC.af = 176 ∧
    frameDrop (act vcpL rfL).af = 176 ∧ (act vcpL rfL).fb.words.size ≤ 0x4000 ∧
    RC.fb.words.size ≤ 0x4000 ∧ RC.fr.size ≤ 176 ∧ (act vcpL rfL).fr.size ≤ 176 ∧
    RC.af.frameSize = 160 ∧ (act vcpL rfL).af.frameSize = 160 := by
  native_decide

theorem scopeLB :
    (act vcpL rfL).vc.blocks.all (·.insts.all (memFormLB (act vcpL rfL).ctx)) = true := by
  native_decide

theorem entryArgsL : entryArgsB vcpL = true := by native_decide

/-! ## The CLIF caller -/

/-- The caller's entry block. -/
def B0C : Clif.Block := fC.blocks.headD default

/-- The caller's entry registers: `v0 = 0`. -/
def regsC : Clif.Regs := (Clif.Regs.empty.setMany (B0C.params.map (·.1)) argsL).getD Clif.Regs.empty

/-- **The caller's CLIF entry state**: block 0, `v0 = 0`, no slots, `memL`. -/
def csC : Clif.State :=
  { frame := { func := fC, regs := regsC, slots := [], body := B0C.body, term := B0C.term }
    callers := []
    mem := memL }

/-- The program: the caller and `%ld`. -/
def pCL : Clif.Program := { funcs := [fC, fL] }

/-- The caller's extern `fn0`. -/
def extF : Clif.ExtFunc := (fC.extern? 0).getD default

/-- The caller suspended at its call (the rest of its block empty, the result `v1`). -/
def extC : List (Clif.Frame × List Clif.ValueId) := [({ csC.frame with body := [] }, [1])]

theorem clifC : B0C.body = [{ results := [1], inst := .call 0 [0] }] ∧
    pCL.func? extF.name = some fL ∧
    (Clif.AbiParam.tys fL.sig.params == Clif.AbiParam.tys extF.sig.params &&
      Clif.AbiParam.tys fL.sig.returns == Clif.AbiParam.tys extF.sig.returns) = true ∧
    fL.entry? = some B0L ∧ argsL.map (·.ty) = Clif.AbiParam.tys fL.sig.params ∧
    argsL.map (·.ty) = B0L.params.map (·.2) ∧ fL.slots = [] := by
  native_decide

/-- The call's operands (as a check). -/
def preB : Bool :=
  match (do
    let ext ← Clif.Res.ofOption s!"unknown function reference fn{(0 : Clif.FnRef)}"
      (csC.frame.func.extern? 0)
    let vals ← csC.frame.getMany [0]
    Clif.checkTys s!"arguments of call to %{ext.name}" vals (Clif.AbiParam.tys ext.sig.params)
    pure (ext, vals) : Clif.Res (Clif.ExtFunc × List Clif.Val)) with
  | .ok a => decide (a = (extF, argsL))
  | _ => false

theorem preB_eq : preB = true := by native_decide

end Concurrency.CallSeg.WitnessC
