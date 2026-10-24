import FV.E2E.MainT
import FV.E2E.FinalTC
import FV.Backend.Proof.StockD0Dispatch
import FV.Backend

/-! # The backend's typed verified scope (S11e5 Stage C, public scope)

The backend (`Backend.compileFileWithLowering`) reports a function verified when
`Backend.unverifiedReason? f = none` and its lowering passed the validator `lowerChecked f true`.
Outside subset E this is now the typed scope: `Backend.verifiableT` (float data movement, float
parameters and returns) with the typed validator `lowerCheckT` (`Backend.lowerCheckFor`).

* `InSubsetT.of_verifiableT`: `verifiableT` gives the typed per-activation subset `InSubsetT`
  (all calls external), as `InSubset.of_verifiable` for `verifiable`.
* `verifiable_or_verifiableT_of_unverifiedReason`: a function reported without reason is in
  `verifiable` or in `verifiableT`.
* `lowerChecked_spec`: a validated lowering of a function of the typed scope is `lowerFunction`'s
  output and passes `lowerCheckT` (and `lowerCheck` on subset E): the `lower`/`lowerOk` fields of
  `CompiledT`/`CompiledCleanupT` (`backend_correct_finalT`, `backend_correct_final_cleanupT`;
  their rule premise is `E2E.typedRules_program`).

S11e6 (#419): outside the typed scope the backend reports a function verified in the scope with
typed direct `try_call`s (`Backend.verifiableTC`, `Compile.functionETC`), validated by
`lowerCheckTC` (`Backend.lowerCheckFor`):

* `InSubsetTC.of_verifiableTC`, `verdict_of_unverifiedReason` (a function reported without reason
  is in `verifiable`, `verifiableT` or `verifiableTC`), `lowerChecked_specTC` (the `lower`/`lowerOk`
  fields of `CompiledTC`, `backend_correct_finalTC`).
* Changed statements (the compiler functions `unverifiedReason?` and `lowerCheckFor` changed, so
  the old statements became false for `functionETC` functions outside `functionET`):
  `verifiable_or_verifiableT_of_unverifiedReason` and `lowerChecked_spec` take the premise that
  `f` is in subset E or the typed scope.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **The typed subset from the backend's typed conditions**, when every call is external to `p`
(`InSubset.of_verifiable` for `InSubsetT`). -/
theorem InSubsetT.of_verifiableT {p : Clif.Program} {f : Clif.Function}
    (h : Backend.verifiableT f = true) (hp : ∀ n, p.func? n = none) : InSubsetT p f := by
  simp only [Backend.verifiableT, Backend.abiSigs, Backend.indSigsOk,
    Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hE, hst, hf, hext, hind⟩ := h
  exact ⟨hE, fun _ _ _ _ _ _ _ e _ => hp e.name,
    fun _ _ _ _ _ _ e _ => hp e.name, ⟨hf, hext⟩, hind, hst⟩

/-- **A function the backend reports without reason is in one of the two scopes**: subset E
(`verifiable`, `E2E.InSubset`) or the typed scope (`verifiableT`, `E2E.InSubsetT`). -/
theorem verifiable_or_verifiableT_of_unverifiedReason {f : Clif.Function}
    (h : Backend.unverifiedReason? f = none)
    (hET : (Compile.functionE f || Compile.functionET f) = true) :
    Backend.verifiable f = true ∨ (Compile.functionE f = false ∧ Backend.verifiableT f = true) := by
  have hC : Compile.functionET f = true → Compile.functionETC f = true :=
    Compile.functionETC_of_functionET
  unfold Backend.unverifiedReason? at h
  cases hE : Compile.functionE f <;> cases hT : Compile.functionET f <;>
    cases hTC : Compile.functionETC f <;>
    cases hs : Compile.storeTypedB f <;> cases ha : Backend.abiSigs f <;>
    cases hi : Backend.indSigsOk f <;>
    simp_all [Backend.verifiable, Backend.verifiableT]

/-- **A function the backend reports without reason is in one of the three scopes**: subset E
(`verifiable`, `E2E.InSubset`), the typed scope (`verifiableT`, `E2E.InSubsetT`) or the scope
with typed direct `try_call`s (`verifiableTC`, `E2E.InSubsetTC`). -/
theorem verdict_of_unverifiedReason {f : Clif.Function}
    (h : Backend.unverifiedReason? f = none) :
    Backend.verifiable f = true ∨ (Compile.functionE f = false ∧ Backend.verifiableT f = true) ∨
      (Compile.functionE f = false ∧ Compile.functionET f = false ∧
        Backend.verifiableTC f = true) := by
  have hC : Compile.functionET f = true → Compile.functionETC f = true :=
    Compile.functionETC_of_functionET
  unfold Backend.unverifiedReason? at h
  cases hE : Compile.functionE f <;> cases hT : Compile.functionET f <;>
    cases hTC : Compile.functionETC f <;>
    cases hs : Compile.storeTypedB f <;> cases ha : Backend.abiSigs f <;>
    cases hi : Backend.indSigsOk f <;>
    simp_all [Backend.verifiable, Backend.verifiableT, Backend.verifiableTC]

/-- **The subset with typed `try_call`s from the backend's conditions**, when every call is
external to `p`. -/
theorem InSubsetTC.of_verifiableTC {p : Clif.Program} {f : Clif.Function}
    (h : Backend.verifiableTC f = true) (hp : ∀ n, p.func? n = none) : InSubsetTC p f := by
  simp only [Backend.verifiableTC, Backend.abiSigs, Backend.indSigsOk,
    Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hE, hst, hf, hext, hind⟩ := h
  exact ⟨hE, fun _ _ _ _ _ _ _ e _ => hp e.name,
    fun _ _ _ _ _ _ e _ => hp e.name, ⟨hf, hext⟩, hind, hst⟩

/-- **The validated lowering**: `lowerChecked f true = .ok vc` is `lowerFunction`'s output, and it
passes the typed validator, and the integer one on subset E. -/
theorem lowerChecked_spec {f : Clif.Function} {vc : VCode}
    (h : Backend.lowerChecked f true = .ok vc)
    (hET : (Compile.functionE f || Compile.functionET f) = true) :
    lowerFunction f = .ok vc ∧ lowerCheckT f vc = true ∧
      (Compile.functionE f = true → lowerCheck f vc = true) := by
  unfold Backend.lowerChecked at h
  rw [Stock.D0.defaultLower_eq_legacy] at h
  cases hl : lowerFunction f with
  | error e => rw [hl] at h; cases h
  | ok vc' =>
    rw [hl] at h
    have hc : Backend.lowerCheckFor f vc' = true := by
      cases hc : Backend.lowerCheckFor f vc'
      · simp [hc] at h <;> cases h
      · rfl
    have hv : vc' = vc := by
      simp [hc] at h
      cases h; rfl
    subst hv
    unfold Backend.lowerCheckFor at hc
    cases hE : Compile.functionE f
    · have hT : Compile.functionET f = true := by simpa [hE] using hET
      simp only [hE, hT, Bool.false_eq_true, ↓reduceIte] at hc
      exact ⟨rfl, hc, fun h => by cases h⟩
    · simp only [hE, ↓reduceIte] at hc
      exact ⟨rfl, lowerCheckT_of_lowerCheck hc, fun _ => hc⟩

/-- **The validated lowering outside the typed scope**: `lowerChecked f true = .ok vc` for a
function outside subset E and `functionET` is `lowerFunction`'s output and passes `lowerCheckTC`
(the `lower`/`lowerOk` fields of `CompiledTC`). -/
theorem lowerChecked_specTC {f : Clif.Function} {vc : VCode}
    (h : Backend.lowerChecked f true = .ok vc) (hE : Compile.functionE f = false)
    (hT : Compile.functionET f = false) :
    lowerFunction f = .ok vc ∧ lowerCheckTC f vc = true := by
  unfold Backend.lowerChecked at h
  rw [Stock.D0.defaultLower_eq_legacy] at h
  cases hl : lowerFunction f with
  | error e => rw [hl] at h; cases h
  | ok vc' =>
    rw [hl] at h
    have hc : Backend.lowerCheckFor f vc' = true := by
      cases hc : Backend.lowerCheckFor f vc'
      · simp [hc] at h <;> cases h
      · rfl
    have hv : vc' = vc := by
      simp [hc] at h
      cases h; rfl
    subst hv
    unfold Backend.lowerCheckFor at hc
    simp only [hE, hT, Bool.false_eq_true, ↓reduceIte] at hc
    exact ⟨rfl, hc⟩

end E2E
