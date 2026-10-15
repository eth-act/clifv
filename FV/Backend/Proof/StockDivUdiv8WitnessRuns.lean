import FV.Backend.Proof.StockDivUdivNarrowSourceValues
namespace Backend.Stock.Proof.ScalarDiv.Udiv8Witness.RunData
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def function : Clif.Function := {
  name := "stock_udiv_complete_source"
  sig := {params := [⟨.i8,.none,.normal⟩,⟨.i8,.none,.normal⟩],returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i8),(31,.i8)],body := [⟨[100],.div .udiv .i8 7 31⟩],term := .ret [100]}] }
def built : Ctx × Array (Nat × Nat) × State := (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)
def sourceKey (info : IInfo) := (info.clif,info.results)
def ctxKey (ctx : Ctx) := (ctx.insts.map sourceKey,ctx.valTy,ctx.valDef,ctx.valReg)
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
theorem observed : (Stock.lower function).toOption.map (fun result =>
    decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 193) &&
    result.blockScans.toList.any (fun event => decide (ctxKey event.ctx = ctxKey built.1) &&
      event.output.records.any (fun record => record.inst == (0 : Nat) &&
        record.output.step.any (fun step => step.decision == .emitted &&
          decide (step.rules.getLast? = some rule_lower_1119.id))))) = some true := by
  decide +kernel
end Kernel
end Backend.Stock.Proof.ScalarDiv.Udiv8Witness.RunData
