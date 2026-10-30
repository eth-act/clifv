import FV.Backend.Proof.StockMinMaxRegisterDriverRuns
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def scalarSelectFunction (cty ty : Clif.Ty) : Clif.Function := {
  name := "stock_select_scalar_original"
  sig := {params := [⟨cty,.none,.normal⟩,⟨ty,.none,.normal⟩,⟨ty,.none,.normal⟩],returns := [⟨ty,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,cty),(31,ty),(63,ty)],body := [⟨[100],.select ty 7 31 63⟩],term := .ret [100]}] }
def scalarSelectBuilt (cty ty : Clif.Ty) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (scalarSelectFunction cty ty)).toOption.getD (sinkCtx,#[],sinkState)
def ScalarSelectObserved (cty ty : Clif.Ty) : Prop :=
  (Stock.lower (scalarSelectFunction cty ty)).toOption.map (fun result =>
    decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 193) &&
    decide (aliasNum result.final.alias 194 = 194) &&
    result.blockScans.toList.any (fun event =>
      decide (minmaxCtxKey event.ctx = minmaxCtxKey (scalarSelectBuilt cty ty).1) &&
      event.output.records.any (fun record => record.inst == (0 : Nat) &&
        record.output.step.any (fun step => step.decision == .emitted &&
          decide (step.rules.getLast? = some rule_lower_2267.id))))) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed8 : ScalarSelectObserved .i8 .i8 ∧ ScalarSelectObserved .i8 .i16 ∧
    ScalarSelectObserved .i8 .i32 ∧ ScalarSelectObserved .i8 .i64 := by
  refine ⟨?_,?_,?_,?_⟩ <;> unfold ScalarSelectObserved <;> decide +kernel
private theorem observed16 : ScalarSelectObserved .i16 .i8 ∧ ScalarSelectObserved .i16 .i16 ∧
    ScalarSelectObserved .i16 .i32 ∧ ScalarSelectObserved .i16 .i64 := by
  refine ⟨?_,?_,?_,?_⟩ <;> unfold ScalarSelectObserved <;> decide +kernel
private theorem observed32 : ScalarSelectObserved .i32 .i8 ∧ ScalarSelectObserved .i32 .i16 ∧
    ScalarSelectObserved .i32 .i32 ∧ ScalarSelectObserved .i32 .i64 := by
  refine ⟨?_,?_,?_,?_⟩ <;> unfold ScalarSelectObserved <;> decide +kernel
private theorem observed64 : ScalarSelectObserved .i64 .i8 ∧ ScalarSelectObserved .i64 .i16 ∧
    ScalarSelectObserved .i64 .i32 ∧ ScalarSelectObserved .i64 .i64 := by
  refine ⟨?_,?_,?_,?_⟩ <;> unfold ScalarSelectObserved <;> decide +kernel
end Kernel
attribute [local irreducible] ScalarSelectObserved
/-- Complete original select drivers retain the real root, source context and
parameter aliases at all16 condition/result width combinations.

Compatibility boundary (S11b, #140): original integer domain only (`f32`/`f64` share widths
with `i32`/`i64`); `conditionInt`/`int` are trailing auto-parameters (`decide`), so the
original call shapes are unchanged. -/
theorem stock_select_scalar_driver_observed (cty ty : Clif.Ty)
    (conditionWidth : cty.width = 8 ∨ cty.width = 16 ∨ cty.width = 32 ∨ cty.width = 64)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (conditionInt : cty.isInt = true := by decide) (int : ty.isInt = true := by decide) :
    ScalarSelectObserved cty ty := by
  cases cty <;> cases ty
  all_goals first
    | exact observed8.1
    | exact observed8.2.1
    | exact observed8.2.2.1
    | exact observed8.2.2.2
    | exact observed16.1
    | exact observed16.2.1
    | exact observed16.2.2.1
    | exact observed16.2.2.2
    | exact observed32.1
    | exact observed32.2.1
    | exact observed32.2.2.1
    | exact observed32.2.2.2
    | exact observed64.1
    | exact observed64.2.1
    | exact observed64.2.2.1
    | exact observed64.2.2.2
    | (simp [Clif.Ty.width] at conditionWidth width; done)
    | (simp at conditionInt int; done)
end Backend.Stock.Proof.ScalarSelect
