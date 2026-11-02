import FV.Link.ResultCallExeWith
import FV.Link.ReturnPinCompilerSourceKernel

namespace Link.LiveCallCompilerWith
open Backend E2E E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false

abbrev input := ReturnPinCompilerFor.input
abbrev attempt := ReturnPinCompilerFor.attemptFor ReturnPinAdmission.liveCalls
abbrev attempt_spec := @ReturnPinCompilerFor.attempt_spec ReturnPinAdmission.liveCalls
abbrev codeMap_leanLink := @ReturnPinCompilerFor.codeMap_leanLink
abbrev leanLink_gotSlot := @ReturnPinCompilerFor.leanLink_gotSlot
abbrev gotOk_leanLink := @ReturnPinCompilerFor.gotOk_leanLink
abbrev outsideAvoids_leanLink := @ReturnPinCompilerFor.outsideAvoids_leanLink
abbrev attempt_correct := @ReturnPinCompilerFor.attempt_correct ReturnPinAdmission.liveCalls
abbrev attempt_correct_depth := @ReturnPinCompilerFor.attempt_correct_depth ReturnPinAdmission.liveCalls
abbrev attempt_correct_peak := @ReturnPinCompilerFor.attempt_correct_peak ReturnPinAdmission.liveCalls
abbrev attempt_correct_source := @ReturnPinCompilerFor.attempt_correct_source ReturnPinAdmission.liveCalls
abbrev attempt_correct_source_peak := @ReturnPinCompilerFor.attempt_correct_source_peak ReturnPinAdmission.liveCalls

/-- Every complete previous ABI attempt retains its exact output. -/
theorem accepts_previous {lower : ProductionLowering} {S : LinkSpec} {cleanup : Bool}
    {file0 file : ByteArray} (previous : ResultCallCompilerWith.attempt lower S file0 cleanup = .ok file) :
    attempt lower S file0 cleanup = .ok file := by
  have extend : ∀ cleanup,okRReturnPinResultCalls (productionStage cleanup) (S.inputProductionWith lower cleanup)
      ((S.inputProductionWith lower cleanup).resultsProductionWith lower cleanup) = true →
      okRReturnPinFor .liveCalls (productionStage cleanup) (S.inputProductionWith lower cleanup)
        ((S.inputProductionWith lower cleanup).resultsProductionWith lower cleanup) = true := by
    intro cleanup checked
    exact okRReturnPinLiveCalls_previous checked
  cases cleanup <;> simp [attempt,ReturnPinCompilerFor.attemptFor,
    ReturnPinAttemptKernel.attemptWith,ResultCallCompilerWith.attempt] at previous ⊢
  all_goals
    split at previous
    · cases previous
    · rename_i scope
      rw [if_neg scope]
      split at previous
      · rename_i checked
        rw [if_pos (extend _ checked)]
        exact previous
      · cases previous

/-- The original semantic attempt remains accepted through the retained previous ABI attempt. -/
theorem accepts_previous_semantic {lower : ProductionLowering} {S : LinkSpec} {cleanup : Bool}
    {file0 file : ByteArray} (previous : SemanticCompilerWith.attempt lower S file0 cleanup = .ok file) :
    attempt lower S file0 cleanup = .ok file :=
  accepts_previous (ResultCallCompilerWith.accepts_previous_semantic previous)

end Link.LiveCallCompilerWith
