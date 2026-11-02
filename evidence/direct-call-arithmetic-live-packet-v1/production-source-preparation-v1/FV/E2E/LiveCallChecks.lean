import FV.E2E.ReturnPinChecksKernel
import FV.E2E.ResultCallChecks

namespace E2E.LiveCallChecks
open LinkCheck
set_option autoImplicit false
set_option Elab.async false
abbrev fnsBProduction := ReturnPinChecksFor.fnsBProductionFor ReturnPinAdmission.liveCalls
abbrev fnsBProduction_append := @ReturnPinChecksFor.fnsBProduction_append ReturnPinAdmission.liveCalls
abbrev checks_iff := @ReturnPinChecksFor.checks_iff ReturnPinAdmission.liveCalls
abbrev okRProduction_of_checks := @ReturnPinChecksFor.okRProduction_of_checks ReturnPinAdmission.liveCalls
abbrev CrateStmtProduction := ReturnPinChecksFor.CrateStmtProduction
abbrev crate_correct_production := @ReturnPinChecksFor.crate_correct_production ReturnPinAdmission.liveCalls

theorem accepts_previous (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool)
    (previous : okRSemanticNI (productionStage cleanup) I (I.resultsProductionWith lower cleanup) = true) :
    okRReturnPinLiveCalls (productionStage cleanup) I (I.resultsProductionWith lower cleanup) = true :=
  okRReturnPinLiveCalls_previous (ResultCallChecks.accepts_previous lower I cleanup previous)
end E2E.LiveCallChecks
