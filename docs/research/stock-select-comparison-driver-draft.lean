import FV.Backend.Proof.StockSelectOriginalSourceValues
import FV.Backend.Proof.StockSelectScalarDriverRuns
namespace Backend.Stock.Proof.ScalarSelect.ComparisonDriverDraft
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def function (cty ty : Clif.Ty) (cc : Clif.IntCC) (extended : Bool) : Clif.Function := {
  name := "stock_select_comparison_original_source"
  sig := {params := [⟨cty,.none,.normal⟩,⟨cty,.none,.normal⟩,⟨ty,.none,.normal⟩,⟨ty,.none,.normal⟩],returns := [⟨ty,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,cty),(31,cty),(63,ty),(95,ty)],body := [⟨[100],.icmp cc cty 7 31⟩] ++ (if extended then [⟨[101],.extend .uextend .i64 100⟩] else []) ++
      [⟨[102],.select ty (if extended then 101 else 100) 63 95⟩],term := .ret [102]}] }
def built (cty ty : Clif.Ty) (cc : Clif.IntCC) (extended : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function cty ty cc extended)).toOption.getD (sinkCtx,#[],sinkState)
def Observed (cty ty : Clif.Ty) (cc : Clif.IntCC) (extended : Bool) : Prop :=
  (Stock.lower (function cty ty cc extended)).toOption.map (fun result =>
    decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 193) &&
    decide (aliasNum result.final.alias 194 = 194) && decide (aliasNum result.final.alias 195 = 195) &&
    result.blockScans.toList.any (fun event =>
      decide (minmaxCtxKey event.ctx = minmaxCtxKey (built cty ty cc extended).1) &&
      event.output.records.any (fun record => record.inst == (if extended then 2 else 1 : Nat) &&
        record.output.step.any (fun step => step.decision == .emitted &&
          decide (step.rules.getLast? = some rule_lower_2267.id))))) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
/-- Complete original direct and zero-extended comparison/select driver runs
retain the original unique select root, source context and all four parameter aliases.
This draft is not yet the complete source-step witness or full scalar matrix. -/
theorem stock_select_comparison_driver_observed_draft (extended : Bool) : Observed .i64 .i64 .ult extended := by
  cases extended <;> unfold Observed <;> decide +kernel
end Kernel
end Backend.Stock.Proof.ScalarSelect.ComparisonDriverDraft
#print axioms Backend.Stock.Proof.ScalarSelect.ComparisonDriverDraft.stock_select_comparison_driver_observed_draft
