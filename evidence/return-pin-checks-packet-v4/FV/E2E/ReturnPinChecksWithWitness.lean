import FV.E2E.ReturnPinChecksWith
import FV.E2E.PreparedReturnPinCallsWitness
import FV.E2E.ProductionBoundaryWitness

namespace E2E.ReturnPinChecksWithWitness
open Backend E2E.LinkCheck E2E.ReturnPinChecksWith
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def original : LinkInput := PreparedReturnPinCallsWitness.input
private def previous (cleanup : Bool) : LinkInput := (ProductionBoundaryWitness.input cleanup).toLinkInput
private def checks (cleanup : Bool) : Bool :=
  SemanticChecksWith.globalBProduction Stock.VoidCall.NI.lowerValidated original cleanup &&
  fnsBProduction Stock.VoidCall.NI.lowerValidated original cleanup (original.funcs.take 1) &&
  fnsBProduction Stock.VoidCall.NI.lowerValidated original cleanup (original.funcs.drop 1) &&
  okRSemanticNI (productionStage cleanup) (previous cleanup)
    ((previous cleanup).resultsProductionWith Stock.Production.lower cleanup)

attribute [local irreducible] checks original previous
-- witness: native_decide (the complete original mixed program and the prior identity fixture only)
private theorem checks_true (cleanup : Bool) : checks cleanup = true := by
  cases cleanup <;> native_decide

private theorem facts (cleanup : Bool) :
    SemanticChecksWith.globalBProduction Stock.VoidCall.NI.lowerValidated original cleanup = true ∧
    fnsBProduction Stock.VoidCall.NI.lowerValidated original cleanup (original.funcs.take 1) = true ∧
    fnsBProduction Stock.VoidCall.NI.lowerValidated original cleanup (original.funcs.drop 1) = true ∧
    okRSemanticNI (productionStage cleanup) (previous cleanup)
      ((previous cleanup).resultsProductionWith Stock.Production.lower cleanup) = true := by
  simpa only [checks,Bool.and_eq_true,and_assoc] using checks_true cleanup

/-- The complete original caller and callee produce the new program theorem through separate slices. -/
-- witness: native_decide (fixed source programs in both cleanup modes)
theorem captured_program (cleanup : Bool) :
    CrateStmtProduction Stock.VoidCall.NI.lowerValidated original cleanup "sret_caller" := by
  have full : fnsBProduction Stock.VoidCall.NI.lowerValidated original cleanup original.funcs = true := by
    rw [← List.take_append_drop 1 original.funcs,fnsBProduction_append]
    exact Bool.and_eq_true.mpr ⟨(facts cleanup).2.1,(facts cleanup).2.2.1⟩
  exact crate_correct_production Stock.VoidCall.NI.lowerValidated original cleanup
    (okRProduction_of_checks (facts cleanup).1 full) _

/-- The previous complete identity program remains accepted by the generated checker. -/
-- witness: native_decide (the unchanged prior identity fixture in both cleanup modes)
theorem previous_program (cleanup : Bool) :
    okRReturnPinCalls (productionStage cleanup) (previous cleanup)
      ((previous cleanup).resultsProductionWith Stock.Production.lower cleanup) = true :=
  accepts_previous Stock.Production.lower (previous cleanup) cleanup (facts cleanup).2.2.2

end E2E.ReturnPinChecksWithWitness
