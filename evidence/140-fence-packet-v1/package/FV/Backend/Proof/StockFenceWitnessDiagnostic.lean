import FV.Backend.Proof.StockFenceSemantics
import FV.Backend.Proof.LowerDecide

namespace Backend.Stock.Proof.FenceFixture
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.lower

/-- A complete source function mixes trapping memory, arithmetic and two fences. -/
def function : Clif.Function := {
  name := "stock_fence_mixed"
  sig := {
    params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩]
    returns := [⟨.i64,.none,.normal⟩]
    callConv := some .systemV }
  blocks := [{id := 0,params := [(7,.i64),(31,.i64)],body := [
    ⟨[63],.load .load .i64 {} 7 0⟩,
    ⟨[],.fence⟩,
    ⟨[100],.binary .iadd .i64 63 31⟩,
    ⟨[],.store .store .i64 {} 100 7 8⟩,
    ⟨[],.fence⟩,
    ⟨[],.trapz 31 .intDivz⟩,
    ⟨[128],.load .load .i64 {} 7 16⟩],term := .ret [128]}]}

#eval (Stock.lower function).map fun result =>
  (lowerScopeB function,dominatedB function,result.blockScans.toList.map fun event =>
    event.output.records.map fun record =>
      (record.inst,reprStr ((event.ctx.insts[record.inst]?).map IInfo.clif),
       reprStr record.output.emitted,record.input.entryColor[record.inst]!))
end Backend.Stock.Proof.FenceFixture
