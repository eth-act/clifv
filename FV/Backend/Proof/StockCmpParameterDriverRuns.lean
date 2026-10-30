import FV.Backend.Proof.StockAliasSemantics
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def cmpParameterFunction : Clif.Function := {
  name := "stock_cmp_complete_parameter_source"
  sig := {params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩],returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64),(31,.i64)],body := [⟨[100],.icmp .eq .i64 7 31⟩],term := .ret [100]}] }
def cmpParameterBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx cmpParameterFunction).toOption.getD (sinkCtx,#[],sinkState)
def cmpSourceKey (info : IInfo) := (info.clif,info.results)
def cmpCtxKey (ctx : Ctx) := (ctx.insts.map cmpSourceKey,ctx.valTy,ctx.valDef,ctx.valReg)
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
/-- A complete actual Stock driver run retains the original comparison record,
real root958 and original source/context identities with stable parameter aliases. -/
theorem stock_cmp_parameter_driver_observed :
    (Stock.lower cmpParameterFunction).toOption.map (fun result =>
      decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 193) &&
      result.blockScans.toList.any (fun event => decide (cmpCtxKey event.ctx = cmpCtxKey cmpParameterBuilt.1) &&
        event.output.records.any (fun record => record.inst == (0 : Nat) &&
          record.output.step.any (fun step => step.decision == .emitted &&
            decide (step.rules.getLast? = some rule_lower_2215.id))))) = some true := by
  decide +kernel
end Kernel
end Backend.Stock.Proof.ScalarCmp
