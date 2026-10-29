module

public import FV.Backend.Proof.StockMinMaxWideDriverRuns

@[expose] public section

namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open MinMaxRegisterFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def wideConstantFunction (unsigned maximum wide left large : Bool) : Clif.Function := {
  name := "stock_minmax_wide_constant_original"
  sig := {params := [⟨wideMinmaxTy wide,.none,.normal⟩],returns := [⟨wideMinmaxTy wide,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(31,wideMinmaxTy wide)],body := [
    ⟨[7],.iconst (wideMinmaxTy wide) (BitVec.ofNat (wideMinmaxTy wide).width (if large then 65537 else 3))⟩,
    ⟨[100],.binary (minmaxOperation unsigned maximum) (wideMinmaxTy wide) (if left then 7 else 31) (if left then 31 else 7)⟩],term := .ret [100]}] }
def wideConstantBuilt (unsigned maximum wide left large : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (wideConstantFunction unsigned maximum wide left large)).toOption.getD (sinkCtx,#[],sinkState)
def wideConstantTarget (wide large : Bool) : Nat := if wide && large then 197 else 196
def wideConstantObserved (unsigned maximum wide left large : Bool) : Prop :=
    (Stock.lower (wideConstantFunction unsigned maximum wide left large)).toOption.map (fun result =>
      decide (aliasNum result.final.alias 192 = 192) &&
      decide (aliasNum result.final.alias 193 = wideConstantTarget wide large) &&
      result.blockScans.toList.any (fun event =>
        decide (minmaxCtxKey event.ctx = minmaxCtxKey (wideConstantBuilt unsigned maximum wide left large).1) &&
        event.output.records.any (fun record => record.inst == (1 : Nat) &&
          record.output.step.any (fun step => step.decision == .emitted &&
            decide (step.rules.getLast? = some (minmaxRule unsigned maximum).id))))) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed_false_false_false (unsigned maximum : Bool) :
    wideConstantObserved unsigned maximum false false false := by
  unfold wideConstantObserved
  cases unsigned <;> cases maximum <;> decide +kernel
private theorem observed_false_false_true (unsigned maximum : Bool) :
    wideConstantObserved unsigned maximum false false true := by
  unfold wideConstantObserved
  cases unsigned <;> cases maximum <;> decide +kernel
private theorem observed_false_true_false (unsigned maximum : Bool) :
    wideConstantObserved unsigned maximum false true false := by
  unfold wideConstantObserved
  cases unsigned <;> cases maximum <;> decide +kernel
private theorem observed_false_true_true (unsigned maximum : Bool) :
    wideConstantObserved unsigned maximum false true true := by
  unfold wideConstantObserved
  cases unsigned <;> cases maximum <;> decide +kernel
private theorem observed_true_false_false (unsigned maximum : Bool) :
    wideConstantObserved unsigned maximum true false false := by
  unfold wideConstantObserved
  cases unsigned <;> cases maximum <;> decide +kernel
private theorem observed_true_false_true (unsigned maximum : Bool) :
    wideConstantObserved unsigned maximum true false true := by
  unfold wideConstantObserved
  cases unsigned <;> cases maximum <;> decide +kernel
private theorem observed_true_true_false (unsigned maximum : Bool) :
    wideConstantObserved unsigned maximum true true false := by
  unfold wideConstantObserved
  cases unsigned <;> cases maximum <;> decide +kernel
private theorem observed_true_true_true (unsigned maximum : Bool) :
    wideConstantObserved unsigned maximum true true true := by
  unfold wideConstantObserved
  cases unsigned <;> cases maximum <;> decide +kernel
end Kernel
/-- Every signed/unsigned min/max operation, width, operand direction and
constant encoding class has an actual retained driver run and checked aliases. -/
theorem stock_minmax_wide_constant_driver_observed (unsigned maximum wide left large : Bool) :
    wideConstantObserved unsigned maximum wide left large := by
  cases wide <;> cases left <;> cases large
  · exact observed_false_false_false unsigned maximum
  · exact observed_false_false_true unsigned maximum
  · exact observed_false_true_false unsigned maximum
  · exact observed_false_true_true unsigned maximum
  · exact observed_true_false_false unsigned maximum
  · exact observed_true_false_true unsigned maximum
  · exact observed_true_true_false unsigned maximum
  · exact observed_true_true_true unsigned maximum
end Backend.Stock.Proof.ScalarSelect
