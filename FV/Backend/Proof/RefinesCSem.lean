import FV.Backend.Proof.RefinesInsts2

/-!
# `Refines` of `csem` (M6 proof)

`refines_csem : Refines F (csem F ctx X)`: on every form `ispec` specifies, `csem` gives the same
def values and control and a `SameWorld` world.

* control forms (`MInst.isCtl`): `csem` states them as `ispec` does;
* a covered form (`csemWF`) on an error-free aligned world: `csem` is the canonical Arm run,
  `refAt_of_wf` dispatches to the per-form `RefAt` lemmas of `RefinesInsts.lean`;
* otherwise `csem` is `mspec`, which is `ispec` wherever `ispec` is defined (`mspec_of_ispec`:
  the memory forms `mspec` adds have no `ispec` arm).
-/

namespace Backend.Proof

open Backend

variable (F : BitVec 64 → Prop) (ctx : FnCtx)

theorem mspec_of_ispec {sb : Nat} {i : MInst} {us : List CV} {w : Arm.ArmState}
    {r : List CV × Arm.ArmState × Ctl} (h : ispec i us w = some r) : mspec sb i us w = some r := by
  unfold mspec
  split
  · simp [ispec] at h
  · simp [ispec] at h
  · simp [ispec] at h
  · exact h

theorem holds_eq (k : CondBrKind) (us : List CV) (w : Arm.ArmState) :
    k.holds us w = condBrHolds k us w := by
  cases k <;> rcases us with _ | ⟨a, _ | ⟨b, _⟩⟩ <;> rfl

set_option maxHeartbeats 4000000 in
/-- The per-form `RefAt` lemmas, by cases on the covered form and the number of use values. -/
theorem refAt_of_wf {i : MInst} {us : List CV} (h : csemWF ctx i us = true) : RefAt F ctx i us := by
  simp only [csemWF, Bool.and_eq_true] at h
  obtain ⟨hf, hl⟩ := h
  unfold FormOk at hf
  split at hf
  all_goals (try cases hf)
  all_goals (try simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hf)
  all_goals (try (rcases hf with hf1 | hf1 <;> subst hf1))
  all_goals (try (obtain ⟨hf1, hf2⟩ := hf))
  all_goals (try subst hf1)
  all_goals (simp [MInst.operands, MInst.visitOperands, OpSpec.def_, OpSpec.use, OpSpec.reuseDef,
      StateT.run, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, bind, StateT.bind,
      Except.bind, pure, StateT.pure, Except.pure, get, getThe, MonadStateOf.get, StateT.get, set,
      StateT.set, useCount, Operand.isUse, xzr_alloc] at hl)
  all_goals (rcases us with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, us⟩⟩⟩⟩ <;> simp at hl)
  all_goals first
    | (first
        | apply ref_aluRRR | apply ref_aluRRR_xn | apply ref_aluRRR_xd | apply ref_aluRRR_xm
        | apply ref_aluRRR_xdm | apply ref_aluRRRR | apply ref_aluRRRR_xa | apply ref_aluRRImm12
        | apply ref_aluRRImm12_xd | apply ref_aluRRImmLogic | apply ref_aluRRImmLogic_xd
        | apply ref_aluRRImmLogic_xn
        | apply ref_aluRRImmShift | apply ref_aluRRRShift | apply ref_aluRRRShift_xd
        | apply ref_aluRRRShift_xn | apply ref_aluRRRExtend | apply ref_aluRRRExtend_xd
        | apply ref_bitRR | apply ref_movWide' | apply ref_movK | apply ref_extend
        | apply ref_bitfieldMove | apply ref_cset | apply ref_csel | apply ref_ccmpImm
        | apply ref_movToFpu | apply ref_movFromVec | apply ref_vecMisc | apply ref_vecLanes
        | apply ref_vecRRR) <;>
      first | assumption | decide
    | (apply refAt_none'; intro w; simp [ispec]; done)

/-- **`Refines` of `csem`**: on every form `ispec` specifies, `csem` agrees with it (same def
values and control, a `SameWorld` world). -/
theorem refines_csem (X : ExtSem) : Refines F (csem F ctx X) := by
  intro i us w outs w' ctl h
  by_cases hc : i.isCtl = true
  · cases i <;> simp only [MInst.isCtl, Bool.false_eq_true] at hc <;> revert h <;>
      rcases us with _ | ⟨a, _ | ⟨b, us⟩⟩ <;> simp [ispec, csem, holds_eq]
    all_goals first
      | (intros; subst_vars; exact ⟨_, ⟨rfl, rfl, rfl⟩, SameWorld.refl F _⟩)
      | (intro h; exact ⟨w', h, SameWorld.refl F _⟩)
  · rw [csem_straight (by simpa using hc)]
    split
    · rename_i hw
      exact refAt_of_wf F ctx hw.1 w outs w' ctl hw.2.1 h
    · exact ⟨w', mspec_of_ispec h, SameWorld.refl F _⟩

end Backend.Proof
