import FV.Link.LiveCallExeWith
import FV.E2E.CallStoreAdmission
import FV.Link.ReturnPinCompilerSourceKernel

namespace Link.CallStoreCompilerWith
open Backend E2E E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false

abbrev input := ReturnPinCompilerFor.input
abbrev attempt := ReturnPinCompilerFor.attemptFor ReturnPinAdmission.callStores
abbrev attempt_spec := @ReturnPinCompilerFor.attempt_spec ReturnPinAdmission.callStores
abbrev codeMap_leanLink := @ReturnPinCompilerFor.codeMap_leanLink
abbrev leanLink_gotSlot := @ReturnPinCompilerFor.leanLink_gotSlot
abbrev gotOk_leanLink := @ReturnPinCompilerFor.gotOk_leanLink
abbrev outsideAvoids_leanLink := @ReturnPinCompilerFor.outsideAvoids_leanLink
abbrev attempt_correct := @ReturnPinCompilerFor.attempt_correct ReturnPinAdmission.callStores
abbrev attempt_correct_depth := @ReturnPinCompilerFor.attempt_correct_depth ReturnPinAdmission.callStores
abbrev attempt_correct_peak := @ReturnPinCompilerFor.attempt_correct_peak ReturnPinAdmission.callStores
abbrev attempt_correct_source := @ReturnPinCompilerFor.attempt_correct_source ReturnPinAdmission.callStores
abbrev attempt_correct_source_peak := @ReturnPinCompilerFor.attempt_correct_source_peak ReturnPinAdmission.callStores

/-- Every complete previous ABI attempt retains its exact output. -/
theorem accepts_previous {lower : ProductionLowering} {S : LinkSpec} {cleanup : Bool}
    {file0 file : ByteArray} (previous : LiveCallCompilerWith.attempt lower S file0 cleanup = .ok file) :
    attempt lower S file0 cleanup = .ok file := by
  have extend : ∀ cleanup,okRReturnPinLiveCalls (productionStage cleanup) (S.inputProductionWith lower cleanup)
      ((S.inputProductionWith lower cleanup).resultsProductionWith lower cleanup) = true →
      okRReturnPinFor .callStores (productionStage cleanup) (S.inputProductionWith lower cleanup)
        ((S.inputProductionWith lower cleanup).resultsProductionWith lower cleanup) = true := by
    intro cleanup checked
    exact okRReturnPinCallStores_previous checked
  cases cleanup <;> simp [attempt,ReturnPinCompilerFor.attemptFor,
    ReturnPinAttemptKernel.attemptWith,LiveCallCompilerWith.attempt] at previous ⊢
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
  accepts_previous (LiveCallCompilerWith.accepts_previous_semantic previous)

end Link.CallStoreCompilerWith
