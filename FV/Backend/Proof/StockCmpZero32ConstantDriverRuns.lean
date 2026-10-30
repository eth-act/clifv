import FV.Backend.Proof.StockAluSelectedValues
import FV.Backend.Proof.StockCmpParameterDriverRuns
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def cmpZeroConstant32Function (nonzero zero : Bool) : Clif.Function := {
  name := "stock_cmp_complete_zero_constant32_source"
  sig := {params := [⟨.i32,.none,.normal⟩],returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i32)],body := [⟨[31],.iconst .i32 (if zero then 0#32 else 3#32)⟩,
    ⟨[63],.iconst .i32 0#32⟩,⟨[100],.icmp (if nonzero then .ne else .eq) .i32 63 31⟩],term := .ret [100]}] }
def cmpZeroConstant32Built (nonzero zero : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (cmpZeroConstant32Function nonzero zero)).toOption.getD (sinkCtx,#[],sinkState)
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
/-- Complete actual both-constant lowering retains original comparison identities
and the demanded constant's real final alias; the looked-through zero stays unmaterialized. -/
theorem stock_cmp_zero_constant32_driver_observed (nonzero zero : Bool) :
    (Stock.lower (cmpZeroConstant32Function nonzero zero)).toOption.map (fun result =>
      decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 197) &&
      result.blockScans.toList.any (fun event => decide (cmpCtxKey event.ctx = cmpCtxKey (cmpZeroConstant32Built nonzero zero).1) &&
        decide ((event.ctx.insts[1]?).map (·.data) = some (.data 152 35 [.data 151 57 [],.int 0])) &&
        event.output.records.any (fun record => record.inst == (2 : Nat) &&
          decide (record.output.state.demand[63]! = 0) &&
          record.output.step.any (fun step => step.decision == .emitted &&
            decide (step.rules.getLast? = some rule_lower_2215.id))))) = some true := by
  cases nonzero <;> cases zero <;> decide +kernel
end Kernel
end Backend.Stock.Proof.ScalarCmp
