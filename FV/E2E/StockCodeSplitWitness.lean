import FV.E2E.StockCodeWorldX
import FV.E2E.StockCodeCfgNI
import FV.Backend.Proof.StockConditionalArgsWitness
import FV.Backend.LinearScan
import FV.Backend.Proof.RegallocCover

/-! Non-vacuity of the code-level consumers on split code: the argument-passing conditional
fixture's actual split code has the code domain, passes the CFG read check, and has the full
checked stage (preparation, checked allocation, physical lowering, emission, layout) in both
cleanup modes. -/

namespace E2E.StockCodeSplitWitness
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

private abbrev function := Backend.Stock.ConditionalArgsCfg.Fixture.function

def checks (cleanup : Bool) : Bool :=
  match Stock.lower function with
  | .error _ => false
  | .ok result =>
    match splitEdgesChecked result.code result.edgeArgs with
    | .error _ => false
    | .ok split =>
      CfgBoundary.check function.sig split.code &&
      match Backend.prepare (Stock.Arithmetic.stage cleanup split.code) with
      | .error _ => false
      | .ok vcp =>
        prepCheck (Stock.Arithmetic.stage cleanup split.code) vcp &&
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

-- witness: native_decide (the fixed function's lowering, split and checked pipeline only)
theorem checks_true : (checks false && checks true) = true := by native_decide

theorem split_code_stage_witness (cleanup : Bool) :
    ∃ result split vcp rf af fa fb,Stock.lower function = .ok result ∧
      splitEdgesChecked result.code result.edgeArgs = .ok split ∧
      Stock.Scalar.CodeDomain function split.code ∧
      CfgBoundary.check function.sig split.code = true ∧
      CompiledStockCodeStage cleanup 0 split.code vcp rf af fa fb ∧
      FormsCovered ⟨fa.k,af.slotBase⟩ vcp := by
  have fixed := checks_true
  simp only [Bool.and_eq_true] at fixed
  have h : checks cleanup = true := by cases cleanup <;> first | exact fixed.1 | exact fixed.2
  unfold checks at h
  cases lowered : Stock.lower function with
  | error message => simp [lowered] at h
  | ok result =>
    simp only [lowered] at h
    cases splitRun : splitEdgesChecked result.code result.edgeArgs with
    | error message => simp [splitRun] at h
    | ok split =>
      simp only [splitRun,Bool.and_eq_true] at h
      obtain ⟨reads,h⟩ := h
      have domain := Backend.Stock.ConditionalArgsCfg.Fixture.conditional_args_witness.1.code lowered splitRun
      cases prepared : Backend.prepare (Stock.Arithmetic.stage cleanup split.code) with
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
              cases emittedLayout : fa.layout with
              | error message => rw [emittedLayout] at layoutOk; change false = true at layoutOk; cases layoutOk
              | ok fb =>
                have check : checkAlloc vcp rf = .ok () := by
                  cases check : checkAlloc vcp rf with
                  | error message => rw [check] at checked; change false = true at checked; cases checked
                  | ok value => cases value; rfl
                exact ⟨result,split,vcp,rf,af,fa,fb,rfl,splitRun,domain,reads,
                  ⟨prepared,prepOk,check,physical,emitted,emittedLayout⟩,
                  (formsCoveredB_iff _ _).mp covered⟩

end E2E.StockCodeSplitWitness
