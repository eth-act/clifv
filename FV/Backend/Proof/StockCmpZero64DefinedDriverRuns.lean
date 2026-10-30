import FV.Backend.Proof.StockAluSelectedValues
import FV.Backend.Proof.StockCmpParameterDriverRuns
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def cmpZeroDefined64Function (nonzero : Bool) : Clif.Function := {
  name := "stock_cmp_complete_zero_defined64_source"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],body := [⟨[31],.unary .ineg .i64 7⟩,
    ⟨[63],.iconst .i64 (BitVec.ofNat 64 0)⟩,⟨[100],.icmp (if nonzero then .ne else .eq) .i64 63 31⟩],term := .ret [100]}] }
def cmpZeroDefined64Built (nonzero : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (cmpZeroDefined64Function nonzero)).toOption.getD (sinkCtx,#[],sinkState)
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
/-- Complete actual lowering retains the defined-operand comparison and its
original identities, with real source alias193-to197 and unmaterialized zero. -/
theorem stock_cmp_zero_defined64_driver_observed (nonzero : Bool) :
    (Stock.lower (cmpZeroDefined64Function nonzero)).toOption.map (fun result =>
      decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 197) &&
      result.blockScans.toList.any (fun event => decide (cmpCtxKey event.ctx = cmpCtxKey (cmpZeroDefined64Built nonzero).1) &&
        decide ((event.ctx.insts[1]?).map (·.data) = some (.data 152 35 [.data 151 57 [],.int 0])) &&
        event.output.records.any (fun record => record.inst == (2 : Nat) &&
          decide (record.output.state.demand[63]! = 0) &&
          record.output.step.any (fun step => step.decision == .emitted &&
            decide (step.rules.getLast? = some rule_lower_2215.id))))) = some true := by
  cases nonzero <;> decide +kernel
end Kernel
end Backend.Stock.Proof.ScalarCmp
