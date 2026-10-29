module

public import FV.Concurrency.CallSegGeo
public import FV.Concurrency.FrameDisjWitness
public import FV.Concurrency.ClifCStepWitness

@[expose] public section

/-!
# Witnesses for `CallSegGeo` (#473, `SegOkG` groundwork)

On the compiled `atomic_load` nested in its compiled caller (`FrameDisj.Witness`):

* `privA_sub_LC`: `Nested.privA_sub` for `nested_LC` (the callee's code is the caller's kept
  addresses `GL`);
* `nested_LE`: the caller with the callee budget exactly the callee's frame (`RCE`) and the
  callee entered there keeping `RCE.FK` (`RLz`) are exactly nested;
* `privA_callee_out_LE`, `privA_callee_LE`: `Nested.privA_callee_out`/`Nested.privA_callee` on
  them (the callee passes no stack arguments: `intBase_eq_zero`);
* `reads_valid_cas`: `cstep_reads_valid` on the `atomic_cas` step of `ClifCStep.Witness`.

Checks by `native_decide` (witness only).
-/

namespace Concurrency.CallSegGeo.Witness

open Arm Backend Backend.Proof E2E FrameDisj FrameDisj.Witness CallSeg.WitnessC
  RealizeCompiled.WitnessL ArmAllocThread
open ArmAllocThread.Witness (act)

/-- The callee's code addresses are the caller's kept addresses. -/
theorem code_RLy : ∀ a, CodeAddr RLy.s0 a → RCK.F a := fun a ha => by
  obtain ⟨j, hj, hd⟩ := CallSeg.WitnessC.codeAddr_words (enterL_program sBC) ha
  have hs := spC.2.2.2.1
  refine Or.inr ?_
  show (a - 0x20000#64).toNat < 4 * (act vcpL rfL).fb.words.size
  generalize (act vcpL rfL).fb.words.size = n at hj hs ⊢
  generalize j = J at hj hd
  bv_omega

/-- **Non-vacuity of `Nested.privA_sub`.** -/
theorem privA_sub_LC : ∀ a, PrivA RLy a → PrivA RCK a :=
  Nested.privA_sub wfRLy nested_LC code_RLy

/-- The caller with the callee budget exactly the callee's frame. -/
def RCE : RL := { RC with K := frameDrop (act vcpL rfL).af }

/-- The callee entered by the caller's `bl ld`, keeping `RCE`'s frame and kept addresses. -/
noncomputable def RLz : RL := { RLx sBC with G := RCE.FK }

theorem nested_LE : Nested RCE RLz where
  sp_le := by
    show (E2E.spv RLy.s0).toNat ≤ (E2E.spv RC.s0 - BitVec.ofNat 64 (frameDrop RC.af)).toNat
    rw [spv_RLy, spv_RC, spC.2.1]; decide
  fits := by
    show (E2E.spv RC.s0 - BitVec.ofNat 64 (frameDrop RC.af)).toNat +
      (frameDrop (act vcpL rfL).af + 0) ≤ (E2E.spv RLy.s0).toNat + frameDrop (act vcpL rfL).af
    rw [spv_RLy, spv_RC, spC.2.1, spC.2.2.1]; decide
  keep := rfl

theorem sp_LE : E2E.spv RLz.s0 = RCE.spB := by
  show E2E.spv RLy.s0 = E2E.spv RC.s0 - BitVec.ofNat 64 (frameDrop RC.af)
  rw [spv_RLy, spv_RC, spC.2.1]; decide

theorem out0L : vcpL.outgoing = 0 := by native_decide

/-- **Non-vacuity of `Nested.privA_callee_out`.** -/
theorem privA_callee_out_LE : ∀ a, PrivA RCE a → PrivA RLz a ∨ slotArea RLz (BitVec.ofNat 64 a) ∨
    (Frame RLz (BitVec.ofNat 64 a) ∧ (BitVec.ofNat 64 a - RLz.spB).toNat < RLz.fr.intBase) :=
  Nested.privA_callee_out stackRLy nested_LE sp_LE rfl

/-- **Non-vacuity of `Nested.privA_callee`.** -/
theorem privA_callee_LE : ∀ a, PrivA RCE a → PrivA RLz a ∨ slotArea RLz (BitVec.ofNat 64 a) :=
  Nested.privA_callee stackRLy nested_LE sp_LE rfl (intBase_eq_zero out0L)

open ClifCStep.Witness in
/-- **Non-vacuity of `cstep_reads_valid`**: the `atomic_cas` step's read and write. -/
theorem reads_valid_cas : (st sCas).mem.valid 0x8000 8 = true := by
  obtain ⟨s', h⟩ := cstep_atomicCas0
  exact cstep_reads_valid h _ (List.mem_cons_self ..) (by decide)

end Concurrency.CallSegGeo.Witness
