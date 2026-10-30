import FV.Backend.Proof.StockMinMaxSourceMatch
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open MinMaxRegisterFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def minmaxSourceKey (info : IInfo) := (info.clif,info.results)
def minmaxCtxKey (ctx : Ctx) := (ctx.insts.map minmaxSourceKey,ctx.valTy,ctx.valDef,ctx.valReg)
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
/-- Complete original64-bit min/max runs retain the real source record, scalar
root and context identities, with unchanged final parameter aliases. -/
theorem stock_minmax_register_driver_observed (unsigned maximum : Bool) :
    (Stock.lower (minmaxFunction unsigned maximum)).toOption.map (fun result =>
      decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 193) &&
      result.blockScans.toList.any (fun event =>
        decide (minmaxCtxKey event.ctx = minmaxCtxKey (minmaxBuilt unsigned maximum).1) &&
        event.output.records.any (fun record => record.inst == (0 : Nat) &&
          record.output.step.any (fun step => step.decision == .emitted &&
            decide (step.rules.getLast? = some (minmaxRule unsigned maximum).id))))) = some true := by
  cases unsigned <;> cases maximum <;> decide +kernel
end Kernel
end Backend.Stock.Proof.ScalarSelect
