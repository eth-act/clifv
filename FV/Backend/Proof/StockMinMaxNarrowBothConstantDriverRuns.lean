import FV.Backend.Proof.StockMinMaxRegisterDriverRuns
import FV.Backend.Proof.StockMinMaxNarrowFixtures
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open MinMaxRegisterFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def narrowBothConstantObserved (unsigned maximum half : Bool) : Prop :=
    (Stock.lower (narrowBothConstantFunction unsigned maximum half)).toOption.map (fun result =>
      decide (aliasNum result.final.alias 192 = narrowBothConstantTargetX half) &&
      decide (aliasNum result.final.alias 193 = narrowBothConstantTargetY half) &&
      result.blockScans.toList.any (fun event =>
        decide (minmaxCtxKey event.ctx = minmaxCtxKey (narrowBothConstantBuilt unsigned maximum half).1) &&
        event.output.records.any (fun record => record.inst == (2 : Nat) &&
          record.output.step.any (fun step => step.decision == .emitted &&
            decide (step.rules.getLast? = some (minmaxRule unsigned maximum).id))))) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed32 (unsigned maximum : Bool) : narrowBothConstantObserved unsigned maximum false := by
  unfold narrowBothConstantObserved
  cases unsigned <;> cases maximum <;> decide +kernel
private theorem observed64 (unsigned maximum : Bool) : narrowBothConstantObserved unsigned maximum true := by
  unfold narrowBothConstantObserved
  cases unsigned <;> cases maximum <;> decide +kernel
end Kernel
/-- Both-constant original minmax inputs inhabit all4 operations at both widths,
with actual retained source/context identities and checked final source aliases. -/
theorem stock_minmax_narrow_both_constant_driver_observed (unsigned maximum half : Bool) :
    narrowBothConstantObserved unsigned maximum half := by
  cases half
  · exact observed32 unsigned maximum
  · exact observed64 unsigned maximum
end Backend.Stock.Proof.ScalarSelect
