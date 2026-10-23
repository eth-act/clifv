import FV.E2E.MainT
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
* `lowerChecked_spec`: a validated lowering is `lowerFunction`'s output and passes `lowerCheckT`
  (and `lowerCheck` on subset E): the `lower`/`lowerOk` fields of `CompiledT`/`CompiledCleanupT`
  (`backend_correct_finalT`, `backend_correct_final_cleanupT`; their rule premise is
  `E2E.typedRules_program`).
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
    (h : Backend.unverifiedReason? f = none) :
    Backend.verifiable f = true ∨ (Compile.functionE f = false ∧ Backend.verifiableT f = true) := by
  unfold Backend.unverifiedReason? at h
  cases hE : Compile.functionE f <;> cases hT : Compile.functionET f <;>
    cases hs : Compile.storeTypedB f <;> cases ha : Backend.abiSigs f <;>
    cases hi : Backend.indSigsOk f <;>
    simp_all [Backend.verifiable, Backend.verifiableT]

/-- **The validated lowering**: `lowerChecked f true = .ok vc` is `lowerFunction`'s output, and it
passes the typed validator, and the integer one on subset E. -/
theorem lowerChecked_spec {f : Clif.Function} {vc : VCode}
    (h : Backend.lowerChecked f true = .ok vc) :
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
      · simp [hc] at h; cases h
      · rfl
    have hv : vc' = vc := by
      simp [hc] at h
      cases h; rfl
    subst hv
    unfold Backend.lowerCheckFor at hc
    cases hE : Compile.functionE f
    · simp only [hE] at hc
      exact ⟨rfl, hc, fun h => by cases h⟩
    · simp only [hE, ↓reduceIte] at hc
      exact ⟨rfl, lowerCheckT_of_lowerCheck hc, fun _ => hc⟩

end E2E
