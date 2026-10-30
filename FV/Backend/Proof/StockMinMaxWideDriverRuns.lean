import FV.Backend.Proof.StockMinMaxRegisterDriverRuns
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open MinMaxRegisterFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def wideMinmaxTy (wide : Bool) : Clif.Ty := if wide then .i64 else .i32
def wideMinmaxFunction (unsigned maximum wide : Bool) : Clif.Function := {
  name := "stock_minmax_wide_original"
  sig := {params := [⟨wideMinmaxTy wide,.none,.normal⟩,⟨wideMinmaxTy wide,.none,.normal⟩],returns := [⟨wideMinmaxTy wide,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,wideMinmaxTy wide),(31,wideMinmaxTy wide)],body := [⟨[100],.binary (minmaxOperation unsigned maximum) (wideMinmaxTy wide) 7 31⟩],term := .ret [100]}] }
def wideMinmaxBuilt (unsigned maximum wide : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (wideMinmaxFunction unsigned maximum wide)).toOption.getD (sinkCtx,#[],sinkState)
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
/-- Complete original32/64-bit min/max runs retain the real source record, scalar
root and context identities, with unchanged final parameter aliases. -/
theorem stock_minmax_wide_driver_observed (unsigned maximum wide : Bool) :
    (Stock.lower (wideMinmaxFunction unsigned maximum wide)).toOption.map (fun result =>
      decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 193) &&
      result.blockScans.toList.any (fun event =>
        decide (minmaxCtxKey event.ctx = minmaxCtxKey (wideMinmaxBuilt unsigned maximum wide).1) &&
        event.output.records.any (fun record => record.inst == (0 : Nat) &&
          record.output.step.any (fun step => step.decision == .emitted &&
            decide (step.rules.getLast? = some (minmaxRule unsigned maximum).id))))) = some true := by
  cases unsigned <;> cases maximum <;> cases wide <;> decide +kernel
end Kernel
end Backend.Stock.Proof.ScalarSelect
