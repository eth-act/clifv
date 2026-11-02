import FV.E2E.ReturnPinAdmission
import FV.E2E.SemanticChecksWith

namespace E2E.ReturnPinChecksFor
variable {admission : E2E.LinkCheck.ReturnPinAdmission}
open Backend E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false

/-- Each slice checks against the complete program and its shared return-pin context. -/
def fnsBProductionFor (admission : ReturnPinAdmission) (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool)
    (fs : List FnInput) : Bool :=
  let R := I.resultsProductionWith lower cleanup
  let C := ReturnPinCtx.of I R
  fs.all fun fi =>
    (chksSemanticFor admission.extra (productionStage cleanup) I (progOf R) (tabOf R)
      fi.func (I.pipeProductionWith lower cleanup fi)).all (·.2) && returnPinsWith C fi.func

local notation "fnsBProduction" => fnsBProductionFor admission

theorem fnsBProduction_append (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool)
    (a b : List FnInput) :
    fnsBProduction lower I cleanup (a ++ b) =
      (fnsBProduction lower I cleanup a && fnsBProduction lower I cleanup b) := by
  simp only [fnsBProduction,List.all_append]

/-- Sliced checks and the whole-program ABI checker have exactly the same success condition. -/
theorem checks_iff (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool) :
    okRReturnPinFor admission (productionStage cleanup) I (I.resultsProductionWith lower cleanup) = true ↔
      E2E.SemanticChecksWith.globalBProduction lower I cleanup = true ∧
      fnsBProduction lower I cleanup I.funcs = true := by
  simp only [okRReturnPinFor, okRSemanticFor,
    E2E.SemanticChecksWith.globalBProduction, fnsBProduction, returnPinsWith_of,
    returnPinChecks, progOf, LinkInput.resultsProductionWith, List.map_map,
    List.all_map, Function.comp_def, Bool.and_eq_true, List.all_eq_true,
    forall_and, and_assoc]

theorem okRProduction_of_checks {lower : ProductionLowering} {I : LinkInput} {cleanup : Bool}
    (global : E2E.SemanticChecksWith.globalBProduction lower I cleanup = true)
    (functions : fnsBProduction lower I cleanup I.funcs = true) :
    okRReturnPinFor admission (productionStage cleanup) I (I.resultsProductionWith lower cleanup) = true :=
  (checks_iff lower I cleanup).mpr ⟨global,functions⟩

def CrateStmtProduction (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool)
    (name : String) : Prop := CrateStmtReturnPins I (I.resultsProductionWith lower cleanup) name

theorem crate_correct_production (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool)
    (checked : okRReturnPinFor admission (productionStage cleanup) I (I.resultsProductionWith lower cleanup) = true)
    (name : String) : CrateStmtProduction lower I cleanup name :=
  preparedReturnPinFor_correct admission (productionStage cleanup) (productionStage_cases cleanup)
    (I.resultsProductionWith_prepared lower cleanup) checked name


end E2E.ReturnPinChecksFor
