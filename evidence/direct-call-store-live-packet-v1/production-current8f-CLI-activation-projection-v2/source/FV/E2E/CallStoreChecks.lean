import FV.E2E.CallStoreAdmission
import FV.E2E.ReturnPinChecksKernel
import FV.E2E.LiveCallChecks

namespace E2E.CallStoreChecks
open LinkCheck
set_option autoImplicit false
set_option Elab.async false
abbrev fnsBProduction := ReturnPinChecksFor.fnsBProductionFor ReturnPinAdmission.callStores
abbrev fnsBProduction_append := @ReturnPinChecksFor.fnsBProduction_append ReturnPinAdmission.callStores
abbrev checks_iff := @ReturnPinChecksFor.checks_iff ReturnPinAdmission.callStores
abbrev okRProduction_of_checks := @ReturnPinChecksFor.okRProduction_of_checks ReturnPinAdmission.callStores
abbrev CrateStmtProduction := ReturnPinChecksFor.CrateStmtProduction
abbrev crate_correct_production := @ReturnPinChecksFor.crate_correct_production ReturnPinAdmission.callStores

theorem accepts_previous (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool)
    (previous : okRSemanticNI (productionStage cleanup) I (I.resultsProductionWith lower cleanup) = true) :
    okRReturnPinCallStores (productionStage cleanup) I (I.resultsProductionWith lower cleanup) = true :=
  okRReturnPinCallStores_previous (LiveCallChecks.accepts_previous lower I cleanup previous)
end E2E.CallStoreChecks
