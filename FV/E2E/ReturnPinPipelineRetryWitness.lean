import FV.E2E.ReturnPinPipelineRetry
import FV.E2E.ReturnPinCheckFastWitness

namespace E2E.ReturnPinPipelineRetryWitness
open Backend Backend.Proof LinkCheck
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- The original captured source retains every successful Stock artifact in both cleanup modes. -/
theorem captured_attempt_retained (cleanup : Bool) :
    PreparedReturnPinSretWitness.input.resultsReturnPins cleanup =
      PreparedReturnPinSretWitness.outputs cleanup := by
  apply LinkInput.resultsReturnPins_accept
  rw [okRReturnPins_eq_fast]
  exact ReturnPinCheckFastWitness.captured_pipeline_passes cleanup

/-- The real incompatible call graph retries every function, not only its callee. -/
theorem mixed_program_retried (cleanup : Bool) :
    PreparedReturnPinCallerBoundaryWitness.input.resultsReturnPins cleanup =
      PreparedReturnPinCallerBoundaryWitness.input.resultsProduction cleanup := by
  apply LinkInput.resultsReturnPins_retry
  exact (PreparedReturnPinCallerBoundaryWitness.legacy_caller_rejected_witness cleanup).2.1

private def previousChecks : Bool :=
  [false,true].all fun cleanup =>
    let I := PreparedReturnPinCallerBoundaryWitness.input
    okRSemanticNI (productionStage cleanup) I (I.resultsProduction cleanup) &&
      (progOf (I.resultsProduction cleanup)).funcs.all (fun g => !hasTls g)

attribute [local irreducible] previousChecks
-- witness: native_decide (the unchanged complete mixed program in both cleanup modes)
private theorem previousChecks_true : previousChecks = true := by native_decide

private theorem previous_checked (cleanup : Bool) :
    okRSemanticNI (productionStage cleanup) PreparedReturnPinCallerBoundaryWitness.input
      (PreparedReturnPinCallerBoundaryWitness.input.resultsProduction cleanup) = true ∧
    (progOf (PreparedReturnPinCallerBoundaryWitness.input.resultsProduction cleanup)).funcs.all
      (fun g => !hasTls g) = true := by
  have both := previousChecks_true
  simp only [previousChecks,List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true] at both
  cases cleanup with
  | false => exact both.1
  | true => exact both.2

/-- The complete mixed program remains accepted after retry, with no additional input condition. -/
theorem mixed_program_accepted (cleanup : Bool) :
    okRReturnPins (productionStage cleanup) PreparedReturnPinCallerBoundaryWitness.input
      (PreparedReturnPinCallerBoundaryWitness.input.resultsReturnPins cleanup) = true :=
  LinkInput.resultsReturnPins_checked _ cleanup (previous_checked cleanup).1

def mixedWorld (cleanup : Bool) : BitVec 64 → Prop :=
  (ofRes PreparedReturnPinCallerBoundaryWitness.input
    (PreparedReturnPinCallerBoundaryWitness.input.resultsReturnPins cleanup)
    closedBase (fun _ => False)).Img

def mixedSystem (cleanup : Bool) : LinkSys :=
  ofRes PreparedReturnPinCallerBoundaryWitness.input
    (PreparedReturnPinCallerBoundaryWitness.input.resultsReturnPins cleanup) closedBase (mixedWorld cleanup)

/-- The entire actual retry result jointly inhabits the ABI-aware system contract. -/
theorem mixed_system_ok (cleanup : Bool) : (mixedSystem cleanup).OkSemanticReturnPins := by
  apply LinkInput.resultsReturnPins_sound _ cleanup (previous_checked cleanup).1
  · apply baseOk_closedR
    intro g member
    have notls : (progOf (PreparedReturnPinCallerBoundaryWitness.input.resultsReturnPins cleanup)).funcs.all
        (fun g => !hasTls g) = true := by
      rw [LinkInput.resultsReturnPins_source]
      exact (previous_checked cleanup).2
    simpa only [Bool.not_eq_true'] using List.all_eq_true.mp notls g member
  · intro a image
    exact image

/-- The actual caller retains the original complete program statement in every valid world. -/
theorem mixed_program_correct (cleanup : Bool) :
    CrateStmtReturnPins PreparedReturnPinCallerBoundaryWitness.input
      (PreparedReturnPinCallerBoundaryWitness.input.resultsReturnPins cleanup) "sret_caller" :=
  LinkInput.resultsReturnPins_correct _ cleanup (previous_checked cleanup).1 "sret_caller"

end E2E.ReturnPinPipelineRetryWitness
