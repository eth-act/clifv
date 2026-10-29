module

public import FV.Backend.Proof.StockCmpParameterDriverRuns

@[expose] public section

namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def cmpNarrow8Function (signed : Bool) : Clif.Function := {
  name := "stock_cmp_complete_parameter_source"
  sig := {params := [⟨.i8,.none,.normal⟩,⟨.i8,.none,.normal⟩],returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i8),(31,.i8)],body := [⟨[100],.icmp (if signed then .slt else .ult) .i8 7 31⟩],term := .ret [100]}] }
def cmpNarrow8Built (signed : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (cmpNarrow8Function signed)).toOption.getD (sinkCtx,#[],sinkState)
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
/-- A complete actual Stock driver run retains the original comparison record,
real root958 and original source/context identities with stable parameter aliases. -/
theorem stock_cmp_narrow8_driver_observed (signed : Bool) :
    (Stock.lower (cmpNarrow8Function signed)).toOption.map (fun result =>
      decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 193) &&
      result.blockScans.toList.any (fun event => decide (cmpCtxKey event.ctx = cmpCtxKey (cmpNarrow8Built signed).1) &&
        event.output.records.any (fun record => record.inst == (0 : Nat) &&
          record.output.step.any (fun step => step.decision == .emitted &&
            decide (step.rules.getLast? = some rule_lower_2215.id))))) = some true := by
  cases signed <;> decide +kernel
end Kernel
end Backend.Stock.Proof.ScalarCmp
