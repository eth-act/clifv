import FV.Backend.Proof.StockAluSelectedValues
import FV.Backend.Proof.StockCmpParameterDriverRuns
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def cmpNonencodable64Function (signed : Bool) : Clif.Function := {
  name := "stock_cmp_complete_immediate_source"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],body := [⟨[31],.iconst .i64 (BitVec.ofNat 64 70003)⟩,
    ⟨[100],.icmp (if signed then .sge else .uge) .i64 7 31⟩],term := .ret [100]}] }
def cmpNonencodable64Built (signed : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (cmpNonencodable64Function signed)).toOption.getD (sinkCtx,#[],sinkState)
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
/-- A complete actual Stock driver run retains the original comparison record,
real root958 and original source/context identities with stable parameter aliases. -/
theorem stock_cmp_nonencodable64_driver_observed (signed : Bool) :
    (Stock.lower (cmpNonencodable64Function signed)).toOption.map (fun result =>
      decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 197) &&
      result.blockScans.toList.any (fun event => decide (cmpCtxKey event.ctx = cmpCtxKey (cmpNonencodable64Built signed).1) &&
        decide ((event.ctx.insts[0]?).map (·.data) = some (.data 152 35 [.data 151 57 [],.int 70003])) &&
        event.output.records.any (fun record => record.inst == (1 : Nat) &&
          decide (0 < record.output.state.demand[31]!) &&
          record.output.step.any (fun step => step.decision == .emitted &&
            decide (step.rules.getLast? = some rule_lower_2215.id))))) = some true := by
  cases signed <;> decide +kernel
end Kernel
end Backend.Stock.Proof.ScalarCmp
