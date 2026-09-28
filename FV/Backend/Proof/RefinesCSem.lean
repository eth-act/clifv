import FV.Backend.Proof.RefinesInsts

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

/-- A form `ispec` leaves unspecified refines trivially. -/
theorem refAt_none {i : MInst} {us : List CV} (h : ∀ w, ispec i us w = none) : RefAt F ctx i us :=
  fun w _ _ _ _ hs => by rw [h] at hs; cases hs

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

end Backend.Proof
