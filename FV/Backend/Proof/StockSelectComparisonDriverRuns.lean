import FV.Backend.Proof.StockMinMaxRegisterDriverRuns
namespace Backend.Stock.Proof.ScalarSelect.ComparisonDriver
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
        decide (record.output.state.demand[100]! = 0) && decide (record.output.state.demand[101]! = 0) &&
        record.output.step.any (fun step => step.decision == .emitted &&
          decide (step.rules.getLast? = some rule_lower_2267.id))))) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed8 (extended : Bool) : Observed .i8 .i8 .ult extended ∧ Observed .i8 .i16 .ult extended ∧ Observed .i8 .i32 .ult extended ∧ Observed .i8 .i64 .ult extended := by
  cases extended
  all_goals refine ⟨?_,?_,?_,?_⟩ <;> unfold Observed <;> decide +kernel
private theorem observed16 (extended : Bool) : Observed .i16 .i8 .ult extended ∧ Observed .i16 .i16 .ult extended ∧ Observed .i16 .i32 .ult extended ∧ Observed .i16 .i64 .ult extended := by
  cases extended
  all_goals refine ⟨?_,?_,?_,?_⟩ <;> unfold Observed <;> decide +kernel
private theorem observed32 (extended : Bool) : Observed .i32 .i8 .ult extended ∧ Observed .i32 .i16 .ult extended ∧ Observed .i32 .i32 .ult extended ∧ Observed .i32 .i64 .ult extended := by
  cases extended
  all_goals refine ⟨?_,?_,?_,?_⟩ <;> unfold Observed <;> decide +kernel
private theorem observed64 (extended : Bool) : Observed .i64 .i8 .ult extended ∧ Observed .i64 .i16 .ult extended ∧ Observed .i64 .i32 .ult extended ∧ Observed .i64 .i64 .ult extended := by
  cases extended
  all_goals refine ⟨?_,?_,?_,?_⟩ <;> unfold Observed <;> decide +kernel
end Kernel
attribute [local irreducible] Observed
/-- Complete direct and zero-extended comparison-select drivers retain the
original select root, source context and parameter aliases at all32 scalar
condition/result-width/form combinations. Complete source-step witnesses follow
from the same actual records in the source witness module.

Compatibility boundary (S11b, #140): original integer domain only (`f32`/`f64` share widths
with `i32`/`i64`); `conditionInt`/`int` are trailing auto-parameters (`decide`), so the
original call shapes are unchanged. -/
theorem stock_select_comparison_driver_observed (cty ty : Clif.Ty) (extended : Bool)
    (comparisonWidth : cty.width = 8 ∨ cty.width = 16 ∨ cty.width = 32 ∨ cty.width = 64)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (conditionInt : cty.isInt = true := by decide) (int : ty.isInt = true := by decide) :
    Observed cty ty .ult extended := by
  cases cty <;> cases ty
  all_goals first
    | exact (observed8 extended).1
    | exact (observed8 extended).2.1
    | exact (observed8 extended).2.2.1
    | exact (observed8 extended).2.2.2
    | exact (observed16 extended).1
    | exact (observed16 extended).2.1
    | exact (observed16 extended).2.2.1
    | exact (observed16 extended).2.2.2
    | exact (observed32 extended).1
    | exact (observed32 extended).2.1
    | exact (observed32 extended).2.2.1
    | exact (observed32 extended).2.2.2
    | exact (observed64 extended).1
    | exact (observed64 extended).2.1
    | exact (observed64 extended).2.2.1
    | exact (observed64 extended).2.2.2
    | (simp [Clif.Ty.width] at comparisonWidth width; done)
    | (simp at conditionInt int; done)
end Backend.Stock.Proof.ScalarSelect.ComparisonDriver
