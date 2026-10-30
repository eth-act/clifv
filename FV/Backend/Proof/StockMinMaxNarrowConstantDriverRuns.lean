import FV.Backend.Proof.StockMinMaxRegisterDriverRuns
import FV.Backend.Proof.StockMinMaxNarrowFixtures
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open MinMaxRegisterFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def narrowConstantObserved (unsigned maximum half left large : Bool) : Prop :=
    (Stock.lower (narrowConstantFunction unsigned maximum half left large)).toOption.map (fun result =>
      decide (aliasNum result.final.alias 192 = 192) &&
      decide (aliasNum result.final.alias 193 = narrowConstantTarget half large) &&
      result.blockScans.toList.any (fun event =>
        decide (minmaxCtxKey event.ctx = minmaxCtxKey (narrowConstantBuilt unsigned maximum half left large).1) &&
        event.output.records.any (fun record => record.inst == (1 : Nat) &&
          record.output.step.any (fun step => step.decision == .emitted &&
            decide (step.rules.getLast? = some (minmaxRule unsigned maximum).id))))) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed_false_false_false (unsigned maximum : Bool) :
    narrowConstantObserved unsigned maximum false false false := by
  unfold narrowConstantObserved
  cases unsigned <;> cases maximum <;> decide +kernel
private theorem observed_false_false_true (unsigned maximum : Bool) :
    narrowConstantObserved unsigned maximum false false true := by
  unfold narrowConstantObserved
  cases unsigned <;> cases maximum <;> decide +kernel
private theorem observed_false_true_false (unsigned maximum : Bool) :
    narrowConstantObserved unsigned maximum false true false := by
  unfold narrowConstantObserved
  cases unsigned <;> cases maximum <;> decide +kernel
private theorem observed_false_true_true (unsigned maximum : Bool) :
    narrowConstantObserved unsigned maximum false true true := by
  unfold narrowConstantObserved
  cases unsigned <;> cases maximum <;> decide +kernel
private theorem observed_true_false_false (unsigned maximum : Bool) :
    narrowConstantObserved unsigned maximum true false false := by
  unfold narrowConstantObserved
  cases unsigned <;> cases maximum <;> decide +kernel
private theorem observed_true_false_true (unsigned maximum : Bool) :
    narrowConstantObserved unsigned maximum true false true := by
  unfold narrowConstantObserved
  cases unsigned <;> cases maximum <;> decide +kernel
private theorem observed_true_true_false (unsigned maximum : Bool) :
    narrowConstantObserved unsigned maximum true true false := by
  unfold narrowConstantObserved
  cases unsigned <;> cases maximum <;> decide +kernel
private theorem observed_true_true_true (unsigned maximum : Bool) :
    narrowConstantObserved unsigned maximum true true true := by
  unfold narrowConstantObserved
  cases unsigned <;> cases maximum <;> decide +kernel
end Kernel
/-- Every signed/unsigned min/max operation, width, operand direction and
constant encoding class has an actual retained driver run and checked aliases. -/
theorem stock_minmax_narrow_constant_driver_observed (unsigned maximum half left large : Bool) :
    narrowConstantObserved unsigned maximum half left large := by
  cases half <;> cases left <;> cases large
  · exact observed_false_false_false unsigned maximum
  · exact observed_false_false_true unsigned maximum
  · exact observed_false_true_false unsigned maximum
  · exact observed_false_true_true unsigned maximum
  · exact observed_true_false_false unsigned maximum
  · exact observed_true_false_true unsigned maximum
  · exact observed_true_true_false unsigned maximum
  · exact observed_true_true_true unsigned maximum
end Backend.Stock.Proof.ScalarSelect
