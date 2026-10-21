import FV.Backend.Proof.StockCmpParameterDriverRuns
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def cmpDefinedFunction : Clif.Function := {
  name := "stock_cmp_complete_defined_source"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],body := [⟨[31],.unary .ineg .i64 7⟩,⟨[100],.icmp .eq .i64 31 7⟩],term := .ret [100]}] }
def cmpDefinedBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx cmpDefinedFunction).toOption.getD (sinkCtx,#[],sinkState)
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
/-- An actual complete Stock run compares a real defined nonconstant operand,
retains its original comparison record/root and resolves the preceding negation
through the real nonidentity alias193→196. -/
theorem stock_cmp_defined_driver_observed :
    (Stock.lower cmpDefinedFunction).toOption.map (fun result =>
      decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 196) &&
      result.blockScans.toList.any (fun event => decide (cmpCtxKey event.ctx = cmpCtxKey cmpDefinedBuilt.1) &&
        event.output.records.any (fun record => record.inst == (1 : Nat) &&
          record.output.step.any (fun step => step.decision == .emitted &&
            decide (step.rules.getLast? = some rule_lower_2215.id))))) = some true := by
  decide +kernel
end Kernel
end Backend.Stock.Proof.ScalarCmp
