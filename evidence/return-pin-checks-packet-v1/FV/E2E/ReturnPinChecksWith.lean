import FV.E2E.PreparedReturnPinCalls
import FV.E2E.SemanticChecksWith

namespace E2E.ReturnPinChecksWith
open Backend E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false

/-- Each slice checks against the complete program and its shared return-pin context. -/
def fnsBProduction (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool)
    (fs : List FnInput) : Bool :=
  let R := I.resultsProductionWith lower cleanup
  let C := ReturnPinCtx.of I R
  fs.all fun fi =>
    (chksSemanticFor returnPinCallsExtra (productionStage cleanup) I (progOf R) (tabOf R)
      fi.func (I.pipeProductionWith lower cleanup fi)).all (·.2) && returnPinsWith C fi.func

theorem fnsBProduction_append (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool)
    (a b : List FnInput) :
    fnsBProduction lower I cleanup (a ++ b) =
      (fnsBProduction lower I cleanup a && fnsBProduction lower I cleanup b) := by
  simp only [fnsBProduction,List.all_append]

/-- Sliced checks and the whole-program ABI checker have exactly the same success condition. -/
theorem checks_iff (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool) :
    okRReturnPinCalls (productionStage cleanup) I (I.resultsProductionWith lower cleanup) = true ↔
      E2E.SemanticChecksWith.globalBProduction lower I cleanup = true ∧
      fnsBProduction lower I cleanup I.funcs = true := by
  constructor
  · intro checked
    simp only [okRReturnPinCalls,okRSemanticFor,Bool.and_eq_true] at checked
    refine ⟨checked.1.1,?_⟩
    simp only [fnsBProduction,List.all_eq_true,Bool.and_eq_true,returnPinsWith_of]
    intro fi member
    have resultMember : (fi.func,I.pipeProductionWith lower cleanup fi) ∈
        I.resultsProductionWith lower cleanup := List.mem_map.mpr ⟨fi,member,rfl⟩
    exact ⟨List.all_eq_true.mp checked.1.2 _ resultMember,
      List.all_eq_true.mp checked.2 _ (List.mem_map.mpr ⟨_,resultMember,rfl⟩)⟩
  · rintro ⟨global,functions⟩
    simp only [fnsBProduction,List.all_eq_true,Bool.and_eq_true,returnPinsWith_of] at functions
    simp only [okRReturnPinCalls,okRSemanticFor,Bool.and_eq_true]
    refine ⟨⟨global,?_⟩,?_⟩
    · simpa only [LinkInput.resultsProductionWith,List.all_map,Function.comp_def] using
        fun fi member => (functions fi member).1
    · simpa only [progOf,LinkInput.resultsProductionWith,List.map_map,List.all_map,Function.comp_def] using
        fun fi member => (functions fi member).2

theorem okRProduction_of_checks {lower : ProductionLowering} {I : LinkInput} {cleanup : Bool}
    (global : E2E.SemanticChecksWith.globalBProduction lower I cleanup = true)
    (functions : fnsBProduction lower I cleanup I.funcs = true) :
    okRReturnPinCalls (productionStage cleanup) I (I.resultsProductionWith lower cleanup) = true :=
  (checks_iff lower I cleanup).mpr ⟨global,functions⟩

def CrateStmtProduction (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool)
    (name : String) : Prop := CrateStmtReturnPins I (I.resultsProductionWith lower cleanup) name

theorem crate_correct_production (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool)
    (checked : okRReturnPinCalls (productionStage cleanup) I (I.resultsProductionWith lower cleanup) = true)
    (name : String) : CrateStmtProduction lower I cleanup name :=
  preparedReturnPinCalls_correct (productionStage cleanup) (productionStage_cases cleanup)
    (I.resultsProductionWith_prepared lower cleanup) checked name

/-- The new generated checker accepts every complete program accepted by its predecessor. -/
theorem accepts_previous (lower : ProductionLowering) (I : LinkInput) (cleanup : Bool)
    (previous : okRSemanticNI (productionStage cleanup) I (I.resultsProductionWith lower cleanup) = true) :
    okRReturnPinCalls (productionStage cleanup) I (I.resultsProductionWith lower cleanup) = true :=
  okRReturnPinCalls_previous (okRReturnPins_of_previous (productionStage cleanup)
    (I.resultsProductionWith_prepared lower cleanup) previous)

end E2E.ReturnPinChecksWith
