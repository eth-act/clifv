import FV.Backend.Proof.StockAluSelectedValues
import FV.Backend.Proof.StockCmpParameterDriverRuns
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def cmpNarrowImmediate8Function (large : Bool) : Clif.Function := {
  name := "stock_cmp_narrow_immediate_source"
  sig := {params := [⟨.i8,.none,.normal⟩],returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i8)],body := [⟨[31],.iconst .i8 (BitVec.ofNat 8 (if large then 129 else 3))⟩,
    ⟨[100],.icmp .ult .i8 7 31⟩],term := .ret [100]}] }
def cmpNarrowImmediate8Built (large : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (cmpNarrowImmediate8Function large)).toOption.getD (sinkCtx,#[],sinkState)
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
/-- Complete actual Stock runs retain the original narrow comparison/root and
leave the immediate source undemanded and unmaterialized, including the
8-bit high-bit constant case. -/
theorem stock_cmp_narrow_immediate8_driver_observed (large : Bool) :
    (Stock.lower (cmpNarrowImmediate8Function large)).toOption.map (fun result =>
      decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 193) &&
      result.blockScans.toList.any (fun event => decide (cmpCtxKey event.ctx = cmpCtxKey (cmpNarrowImmediate8Built large).1) &&
        decide ((event.ctx.insts[0]?).map (·.data) = some (.data 152 35 [.data 151 57 [],.int (if large then 129 else 3)])) &&
        event.output.records.any (fun record => record.inst == (1 : Nat) &&
          decide (record.output.state.demand[31]! = 0) &&
          record.output.step.any (fun step => step.decision == .emitted &&
            decide (step.rules.getLast? = some rule_lower_2215.id))))) = some true := by
  cases large <;> decide +kernel
end Kernel
end Backend.Stock.Proof.ScalarCmp
