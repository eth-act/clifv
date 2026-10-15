import FV.Backend.Proof.StockMinMaxWideDriverRuns
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open MinMaxRegisterFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def wideBothConstantFunction (unsigned maximum wide : Bool) : Clif.Function := {
  name := "stock_minmax_wide_both_constant_original"
  sig := {returns := [⟨wideMinmaxTy wide,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [],body := [
    ⟨[7],.iconst (wideMinmaxTy wide) (BitVec.ofNat (wideMinmaxTy wide).width 3)⟩,
    ⟨[31],.iconst (wideMinmaxTy wide) (BitVec.ofNat (wideMinmaxTy wide).width 65537)⟩,
    ⟨[100],.binary (minmaxOperation unsigned maximum) (wideMinmaxTy wide) 7 31⟩],term := .ret [100]}] }
def wideBothConstantBuilt (unsigned maximum wide : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (wideBothConstantFunction unsigned maximum wide)).toOption.getD (sinkCtx,#[],sinkState)
def wideBothConstantTargetX (wide : Bool) : Nat := if wide then 198 else 197
def wideBothConstantTargetY (wide : Bool) : Nat := if wide then 197 else 196
def wideBothConstantObserved (unsigned maximum wide : Bool) : Prop :=
    (Stock.lower (wideBothConstantFunction unsigned maximum wide)).toOption.map (fun result =>
      decide (aliasNum result.final.alias 192 = wideBothConstantTargetX wide) &&
      decide (aliasNum result.final.alias 193 = wideBothConstantTargetY wide) &&
      result.blockScans.toList.any (fun event =>
        decide (minmaxCtxKey event.ctx = minmaxCtxKey (wideBothConstantBuilt unsigned maximum wide).1) &&
        event.output.records.any (fun record => record.inst == (2 : Nat) &&
          record.output.step.any (fun step => step.decision == .emitted &&
            decide (step.rules.getLast? = some (minmaxRule unsigned maximum).id))))) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed32 (unsigned maximum : Bool) : wideBothConstantObserved unsigned maximum false := by
  unfold wideBothConstantObserved
  cases unsigned <;> cases maximum <;> decide +kernel
private theorem observed64 (unsigned maximum : Bool) : wideBothConstantObserved unsigned maximum true := by
  unfold wideBothConstantObserved
  cases unsigned <;> cases maximum <;> decide +kernel
end Kernel
/-- Both-constant original minmax inputs inhabit all4 operations at both widths,
with actual retained source/context identities and checked final source aliases. -/
theorem stock_minmax_wide_both_constant_driver_observed (unsigned maximum wide : Bool) :
    wideBothConstantObserved unsigned maximum wide := by
  cases wide
  · exact observed32 unsigned maximum
  · exact observed64 unsigned maximum
end Backend.Stock.Proof.ScalarSelect
