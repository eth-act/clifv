import FV.E2E.CompiledSemantic
import FV.E2E.StockArithmeticArtifactWitness
import FV.Backend.Proof.ArithmeticProduction

namespace E2E.StockArithmeticStageWitness
open Backend Backend.Proof Backend.Proof.Driver
open StockArithmeticArtifactWitness (function)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private def checks (cleanup : Bool) : Bool :=
  Stock.Arithmetic.sourceOk function &&
  match Stock.lower function with
  | .error _ => false
  | .ok result =>
    !lowerCheck function result.code && Stock.Arithmetic.check function result.code &&
    (match Stock.Arithmetic.lowerCandidate function with
      | .error _ => false
      | .ok vc => decide (vc = result.code)) &&
    match Backend.prepare (Stock.Arithmetic.stage cleanup result.code) with
    | .error _ => false
    | .ok vcp =>
      prepCheck (Stock.Arithmetic.stage cleanup result.code) vcp &&
      match leanAlloc vcp with
      | .error _ => false
      | .ok rf =>
        (checkAlloc vcp rf).isOk &&
        match lowerRFunc vcp rf with
        | .error _ => false
        | .ok af =>
          match emitFunc 0 af with
          | .error _ => false
          | .ok fa => formsCoveredB ⟨fa.k,af.slotBase⟩ vcp && fa.layout.isOk

/-- Fixed compiler data only. Both cleanup modes finish the actual raw Stock
path, including an unused argument/explicit slot, beyond the legacy checker. -/
theorem checks_true : (checks false && checks true) = true := by native_decide

/-- The source checker, semantic sum and transactional lowering are jointly
inhabited by the real artifact in each existing cleanup setting. -/
theorem compiled_exists (cleanup : Bool) :
    Stock.Arithmetic.Domain function ∧
    ∃ result vcp rf af fa fb,
      CompiledStockArithmeticStage function cleanup 0 result vcp rf af fa fb ∧
      CompiledSemantic function 0 result.code vcp rf af fa fb ∧
      lowerCheckedSemanticWith Stock.Arithmetic.lowerCandidate function true = .ok result.code ∧
      leanAlloc vcp = .ok rf ∧ FormsCovered ⟨fa.k,af.slotBase⟩ vcp ∧
      lowerCheck function result.code = false := by
  have h : checks cleanup = true := by
    have both := checks_true
    simp only [Bool.and_eq_true] at both
    cases cleanup with
    | false => exact both.1
    | true => exact both.2
  simp only [checks,Bool.and_eq_true] at h
  obtain ⟨source,h⟩ := h
  refine ⟨Stock.Arithmetic.sourceOk_sound source,?_⟩
  cases lowered : Stock.lower function with
  | error message => simp [lowered] at h
  | ok result =>
    simp only [lowered,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq] at h
    obtain ⟨⟨⟨legacy,semantic⟩,candidate⟩,h⟩ := h
    have candidateRun : Stock.Arithmetic.lowerCandidate function = .ok result.code := by
      cases candidateRun : Stock.Arithmetic.lowerCandidate function with
      | error message => simp [candidateRun] at candidate
      | ok vc =>
        have same : vc = result.code := by simpa only [candidateRun,decide_eq_true_eq] using candidate
        simpa only [same] using candidateRun
    cases prepared : Backend.prepare (Stock.Arithmetic.stage cleanup result.code) with
    | error message => simp [prepared] at h
    | ok vcp =>
      simp only [prepared,Bool.and_eq_true] at h
      obtain ⟨prepOk,h⟩ := h
      cases allocated : leanAlloc vcp with
      | error message => simp [allocated] at h
      | ok rf =>
        simp only [allocated,Bool.and_eq_true] at h
        obtain ⟨checked,h⟩ := h
        cases physical : lowerRFunc vcp rf with
        | error message => simp [physical] at h
        | ok af =>
          cases emitted : emitFunc 0 af with
          | error message => simp [physical,emitted] at h
          | ok fa =>
            simp only [physical,emitted,Bool.and_eq_true] at h
            obtain ⟨covered,layoutOk⟩ := h
            cases layout : fa.layout with
            | error message => rw [layout] at layoutOk; change false = true at layoutOk; cases layoutOk
            | ok fb =>
              have check : checkAlloc vcp rf = .ok () := by
                cases check : checkAlloc vcp rf with
                | error message => rw [check] at checked; change false = true at checked; cases checked
                | ok value => cases value; rfl
              exact ⟨result,vcp,rf,af,fa,fb,
                ⟨lowered,prepared,prepOk,check,physical,emitted,layout⟩,
                CompiledSemantic.of_checks semantic
                  (by rwa [Stock.Arithmetic.stageF_of_lowerCheck_false legacy])
                  (by rwa [Stock.Arithmetic.stageF_of_lowerCheck_false legacy])
                  check physical emitted layout,
                lowerCheckedSemanticWith_success candidateRun semantic,
                allocated,(formsCoveredB_iff _ _).mp covered,legacy⟩

end E2E.StockArithmeticStageWitness
