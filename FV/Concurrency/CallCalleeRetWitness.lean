import FV.Concurrency.CallCalleeRet
import FV.Concurrency.CallEntryPremisesWitness
import FV.Concurrency.CallRetResumeWitness

/-!
# Witness: the callee's return contract and the caller's resume premises (#473, step (3))

On the compiled caller of `atomic_load` (`CallSeg.WitnessC.RC`) at its `bl` (`sBF`) and the
compiled `atomic_load` entered there (`RLx sBF`, ABI entry `enterL sBF`), with a callee return
state returning `42` in `x0` (`CallRetResume.Witness.yX`):

* `retC_RX`: `ArmAllocThread.RetC` of the callee holds at `yX` (the return address after the
  `bl`, the checker entry values the caller's registers at the `bl`);
* **`resume_premises_RX`**: `ArmAllocThread.resume_premises_of_retC` discharges every premise
  (the entry agreement `r_enterL`/`xreg30_enterL`/`mem_enterL`, the callee's kept addresses
  `RC.F ⊇ RC.FK`, the checker entry values from `entry_premises_L`, the call's defs `defsC1`).

Checks by `native_decide`/`decide` (witness only).
-/

namespace Concurrency.CallRetResume.Witness

open Arm ArmThread Backend Backend.Proof VCodeThread AllocThread ArmAllocThread E2E CallSeg
  CallSeg.WitnessC CallResumeL CallResumeL.Witness

/-- **The callee's return contract at `yX`.** -/
theorem retC_RX : RetC (RLx sBF) (Arm.r .PC sBF + 4#64) (fun r => regVal sBF r) yX := by
  obtain ⟨m, -, hq, -⟩ := prefixF
  refine ⟨?_, ?_, ?_, fun a _ => ?_, ?_, fun r hr => by rw [regVal_yX hr]⟩
  · simp [yX, yR, r_of_w_different]
  · unfold yX yR
    rw [r_of_w_different (by simp), r_of_w_different (by simp)]
    exact (q_stRel hq).err
  · show spOf yX = Arm.r (.GPR 31#5) (enterL sBF)
    rw [spOf_yX, r_enterL (by simp) (by simp)]; rfl
  · show yX.mem a = (enterL sBF).mem a
    rw [mem_yX, mem_enterL]
  · show Arm.r (.GPR 29#5) yX = Arm.r (.GPR 29#5) (enterL sBF)
    unfold yX yR
    rw [r_of_w_different (by simp), r_of_w_different (by simp), r_enterL (by simp) (by simp)]

/-- **The caller's resume premises from the callee's return contract** (module doc). -/
theorem resume_premises_RX :
    Arm.r .PC yX = Arm.r .PC sBF + 4#64 ∧ Arm.r .ERR yX = .None ∧ spOf yX = spOf sBF ∧
      (∀ a, RC.FK a → yX.mem a = sBF.mem a) ∧
      (∀ l, ValidLoc l → Live RC.rf l → (∀ c ∈ (MInst.call infoC1).clobbers, l ≠ .reg c) →
        (∀ q ∈ defPairs opsC1 #[.reg (.x 0), .reg (.x 0)], q.1.isLate = true → q.2 ≠ l) →
        locVal RC.fr yX l = locVal RC.fr sBF l) ∧
      (∀ c ∈ (MInst.call infoC1).clobbers, c ∈ calleeSaved →
        ckeep c (regVal yX c) = ckeep c (regVal sBF c)) ∧ xreg 29 yX = xreg 29 sBF := by
  obtain ⟨m, -, hq, -⟩ := prefixF
  have hS := q_stRel hq
  exact resume_premises_of_retC wfRC (wfX hS) (abiX hS) retC_RX hS
    (fun f h1 h2 => r_enterL h1 h2 sBF) (xreg30_enterL sBF)
    (fun a _ => by show (enterL sBF).mem a = _; rw [mem_enterL])
    (fun a ha => show RC.F a from RL.FK_F ha)
    (fun r hr => ((entry_premises_L hS).1 r hr).symm) defsC1

end Concurrency.CallRetResume.Witness
