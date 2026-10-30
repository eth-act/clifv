import FV.Backend.Proof.StockAluSelectedValues
import FV.Backend.Proof.StockCmpParameterDriverRuns
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
def cmpNarrowConstant16SignedZeroFunction : Clif.Function := {
  name := "stock_cmp_complete_immediate_source"
  sig := {params := [⟨.i16,.none,.normal⟩],returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i16)],body := [⟨[31],.iconst .i16 (BitVec.ofNat 16 0)⟩,
    ⟨[100],.icmp .sge .i16 7 31⟩],term := .ret [100]}] }
def cmpNarrowConstant16SignedZeroBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (cmpNarrowConstant16SignedZeroFunction)).toOption.getD (sinkCtx,#[],sinkState)
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
/-- A complete actual Stock driver run retains the original comparison record,
real root958 and original source/context identities with a materialized constant final alias193→197. -/
theorem stock_cmp_narrow_constant16_signedzero_driver_observed :
    (Stock.lower (cmpNarrowConstant16SignedZeroFunction)).toOption.map (fun result =>
      decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 197) &&
      result.blockScans.toList.any (fun event => decide (cmpCtxKey event.ctx = cmpCtxKey (cmpNarrowConstant16SignedZeroBuilt).1) &&
        decide ((event.ctx.insts[0]?).map (·.data) = some (.data 152 35 [.data 151 57 [],.int 0])) &&
        event.output.records.any (fun record => record.inst == (1 : Nat) &&
          decide (0 < record.output.state.demand[31]!) &&
          record.output.step.any (fun step => step.decision == .emitted &&
            decide (step.rules.getLast? = some rule_lower_2215.id))))) = some true := by
  decide +kernel
end Kernel
end Backend.Stock.Proof.ScalarCmp
