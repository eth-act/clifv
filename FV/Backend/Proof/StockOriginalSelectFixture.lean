import FV.Backend.Proof.StockMinMaxRegisterDriverRuns
namespace Backend.Stock.Proof.ScalarSelect.OriginalSelectFixture
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def function : Clif.Function := {
  name := "stock_select_original_source"
  sig := {params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64),(31,.i64),(63,.i64)],body := [⟨[100],.select .i64 7 31 63⟩],term := .ret [100]}] }
def built : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
/-- Complete original three-parameter source input lowers through the real
select root and retains its original context and final parameter aliases. -/
theorem stock_original_select_driver_observed :
    (Stock.lower function).toOption.map (fun result =>
      decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 193) &&
      decide (aliasNum result.final.alias 194 = 194) &&
      result.blockScans.toList.any (fun event =>
        decide (minmaxCtxKey event.ctx = minmaxCtxKey built.1) &&
        event.output.records.any (fun record => record.inst == (0 : Nat) &&
          record.output.step.any (fun step => step.decision == .emitted &&
            decide (step.rules.getLast? = some rule_lower_2267.id))))) = some true := by
  decide +kernel
end Kernel
end Backend.Stock.Proof.ScalarSelect.OriginalSelectFixture
