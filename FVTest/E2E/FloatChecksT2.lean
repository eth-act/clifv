module

public import FVTest.E2E.FloatScopeT2
public import FV.E2E.LinkScopeChecksT2

@[expose] public section

/-!
# Witnesses: the typed coverage checks on `fnScopeInTB2` (S11 #35)

`fW` (a float function of `fnScopeInTB2`, `FloatScopeT2`) lowers and prepares (checked by
`native_decide`, witness only); `resClassOkB_of_T2` and `formsCoveredB_of_T2` then give its
`resClassOkB` and `formsCoveredB` without running them.
-/

namespace FloatChecksT2

open Backend Backend.Proof E2E.LinkCheck FloatFinalT FloatScopeT2

/-- `fW` lowers and prepares. -/
theorem fW_pipeline : ∃ vc vcp, lowerFunction fW = .ok vc ∧ prepare vc = .ok vcp := by
  have h : (match lowerFunction fW with
    | .ok vc => (prepare vc).toBool
    | .error _ => false) = true := by native_decide
  cases hl : lowerFunction fW with
  | error e => rw [hl] at h; cases h
  | ok vc =>
    rw [hl] at h
    simp only at h
    cases hp : prepare vc with
    | error e => rw [hp] at h; cases h
    | ok vcp => exact ⟨vc, vcp, rfl, hp⟩

theorem fW_resClass : Spill.resClassOkB fW = true := resClassOkB_of_T2 fnScopeInTB2_w

theorem fW_formsCovered : ∃ vc vcp, lowerFunction fW = .ok vc ∧ prepare vc = .ok vcp ∧
    formsCoveredB default vcp = true := by
  obtain ⟨vc, vcp, hl, hp⟩ := fW_pipeline
  exact ⟨vc, vcp, hl, hp, formsCoveredB_of_T2 fnScopeInTB2_w hl hp default⟩

end FloatChecksT2
