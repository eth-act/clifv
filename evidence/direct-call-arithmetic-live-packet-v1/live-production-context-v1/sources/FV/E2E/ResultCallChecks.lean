import FV.E2E.ReturnPinChecksKernel
import FV.E2E.ReturnPinChecksWith

namespace E2E.ResultCallChecks
open LinkCheck
set_option autoImplicit false
set_option Elab.async false
abbrev fnsBProduction := ReturnPinChecksFor.fnsBProductionFor ReturnPinAdmission.resultCalls
abbrev fnsBProduction_append := @ReturnPinChecksFor.fnsBProduction_append ReturnPinAdmission.resultCalls
abbrev checks_iff := @ReturnPinChecksFor.checks_iff ReturnPinAdmission.resultCalls
abbrev okRProduction_of_checks := @ReturnPinChecksFor.okRProduction_of_checks ReturnPinAdmission.resultCalls
abbrev CrateStmtProduction := ReturnPinChecksFor.CrateStmtProduction
abbrev crate_correct_production := @ReturnPinChecksFor.crate_correct_production ReturnPinAdmission.resultCalls

theorem accepts_previous (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool)
    (previous : okRSemanticNI (productionStage cleanup) I (I.resultsProductionWith lower cleanup) = true) :
    okRReturnPinResultCalls (productionStage cleanup) I (I.resultsProductionWith lower cleanup) = true :=
  okRReturnPinResultCalls_previous (ReturnPinChecksWith.accepts_previous lower I cleanup previous)
end E2E.ResultCallChecks
