import FV.E2E.PreparedReturnPinCallerBoundaryWitness

namespace E2E.ReturnPinCheckFastWitness
open Backend LinkCheck
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def capturedChecks : Bool :=
  [false,true].all fun cleanup => okRReturnPinsFast (productionStage cleanup)
    PreparedReturnPinSretWitness.input (PreparedReturnPinSretWitness.outputs cleanup)

attribute [local irreducible] capturedChecks
-- witness: native_decide (the unchanged captured source in both cleanup modes)
private theorem capturedChecks_true : capturedChecks = true := by native_decide

/-- The executable fast checker accepts the complete original sret capture in both modes. -/
theorem captured_pipeline_passes (cleanup : Bool) :
    okRReturnPinsFast (productionStage cleanup) PreparedReturnPinSretWitness.input
      (PreparedReturnPinSretWitness.outputs cleanup) = true := by
  have checked := capturedChecks_true
  simp only [capturedChecks,List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true] at checked
  cases cleanup with
  | false => exact checked.1
  | true => exact checked.2

/-- Caching preserves the rejection of a real legacy caller paired with a Stock sret callee. -/
theorem mixed_pipeline_rejected (cleanup : Bool) :
    okRReturnPinsFast (productionStage cleanup) PreparedReturnPinCallerBoundaryWitness.input
      (PreparedReturnPinCallerBoundaryWitness.outputs cleanup) = false := by
  rw [← okRReturnPins_eq_fast]
  exact (PreparedReturnPinCallerBoundaryWitness.legacy_caller_rejected_witness cleanup).2.1

/-- The accepted fast verdict supplies the same original whole-program guarantee. -/
theorem captured_program_correct (cleanup : Bool) :
    CrateStmtReturnPins PreparedReturnPinSretWitness.input
      (PreparedReturnPinSretWitness.outputs cleanup) Stock.Memory.StoreRoots.ComputedFixture.function.name :=
  PreparedReturnPinSretWitness.program_correct cleanup

end E2E.ReturnPinCheckFastWitness
