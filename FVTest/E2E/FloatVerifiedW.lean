import FV.E2E.VerifiableT
import FVTest.E2E.FloatFinalT
import FV.E2E.LinkCheck

/-!
Non-vacuity of the backend's typed verified scope (S11e5 Stage C, public scope): the float
functions `fW` (float data movement between integer parameters and an integer return) and `fMv`
(float parameters and a float return) of `FVTest/E2E/FloatFinalT.lean` are outside subset E, the
backend reports them without reason (`unverifiedReason? = none`: `verifiableT`), and their
validated lowering `lowerChecked f true` succeeds; so `InSubsetT.of_verifiableT` and
`lowerChecked_spec` apply. Checks by `native_decide` (witness only).
`lake build FVTest.E2E.FloatVerifiedW`.
-/

open Backend Backend.Proof.Driver E2E E2E.LinkCheck

namespace FloatVerifiedW

open FloatFinalT
open FloatDriverT (fMv)

def checks : Bool :=
  !Compile.functionE fW && (unverifiedReason? fW).isNone && verifiableT fW &&
  (lowerChecked fW true).toBool &&
  !Compile.functionE fMv && (unverifiedReason? fMv).isNone && verifiableT fMv &&
  (lowerChecked fMv true).toBool

theorem checks_true : checks = true := by native_decide

theorem parts : Compile.functionE fW = false ∧ unverifiedReason? fW = none ∧
    verifiableT fW = true ∧ (lowerChecked fW true).toBool = true ∧
    Compile.functionE fMv = false ∧ unverifiedReason? fMv = none ∧ verifiableT fMv = true ∧
    (lowerChecked fMv true).toBool = true := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2,
    h.2⟩

/-- **Witness**: `fW` is reported without reason, in the typed scope only. -/
theorem reason_w :
    Backend.verifiable fW = true ∨ (Compile.functionE fW = false ∧ Backend.verifiableT fW = true) :=
  verifiable_or_verifiableT_of_unverifiedReason parts.2.1

/-- **Witness**: the typed subset of `fW` in a program without functions. -/
theorem inSubsetT_w : InSubsetT { funcs := [] } fW :=
  InSubsetT.of_verifiableT parts.2.2.1 fun _ => rfl

/-- **Witness**: `fW`'s validated lowering passes `lowerCheckT`. -/
theorem lowerChecked_w :
    lowerFunction fW = .ok (getOk (lowerChecked fW true)) ∧
      lowerCheckT fW (getOk (lowerChecked fW true)) = true :=
  let h := lowerChecked_spec (getOk_eq parts.2.2.2.1)
  ⟨h.1, h.2.1⟩

/-- **Witness**: `fMv` (float parameters and return) is reported without reason. -/
theorem reason_mv :
    Backend.verifiable fMv = true ∨
      (Compile.functionE fMv = false ∧ Backend.verifiableT fMv = true) :=
  verifiable_or_verifiableT_of_unverifiedReason parts.2.2.2.2.2.1

/-- **Witness**: `fMv`'s validated lowering passes `lowerCheckT`. -/
theorem lowerChecked_mv :
    lowerFunction fMv = .ok (getOk (lowerChecked fMv true)) ∧
      lowerCheckT fMv (getOk (lowerChecked fMv true)) = true :=
  let h := lowerChecked_spec (getOk_eq parts.2.2.2.2.2.2.2)
  ⟨h.1, h.2.1⟩

end FloatVerifiedW
