import FV.Backend.Proof.StockAluSelectedValues
import FV.Backend.Proof.StockCmpParameterDriverRuns
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def cmpBothNonzero32Function : Clif.Function := {
  name := "stock_cmp_complete_both_nonzero32_source"
  sig := {params := [⟨.i32,.none,.normal⟩],returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i32)],body := [⟨[31],.iconst .i32 3#32⟩,
    ⟨[63],.iconst .i32 5#32⟩,⟨[100],.icmp .eq .i32 31 63⟩],term := .ret [100]}] }
def cmpBothNonzero32Built : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (cmpBothNonzero32Function)).toOption.getD (sinkCtx,#[],sinkState)
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
/-- Complete actual both-constant lowering retains original comparison identities
and the demanded constant's real final alias; the looked-through nonzero right constant stays unmaterialized. -/
theorem stock_cmp_both_nonzero32_driver_observed :
    (Stock.lower (cmpBothNonzero32Function)).toOption.map (fun result =>
      decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 197) &&
      result.blockScans.toList.any (fun event => decide (cmpCtxKey event.ctx = cmpCtxKey (cmpBothNonzero32Built).1) &&
        decide ((event.ctx.insts[1]?).map (·.data) = some (.data 152 35 [.data 151 57 [],.int 5])) &&
        event.output.records.any (fun record => record.inst == (2 : Nat) &&
          decide (record.output.state.demand[63]! = 0) &&
          record.output.step.any (fun step => step.decision == .emitted &&
            decide (step.rules.getLast? = some rule_lower_2215.id))))) = some true := by
  decide +kernel
end Kernel
end Backend.Stock.Proof.ScalarCmp
