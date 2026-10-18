import FV.Backend.Proof.StockEmissionCoverageFixture
import FV.Backend.Proof.StockRecordFormCoverage

namespace Backend.Stock.Proof.BindingCoverageWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.EmissionCoverageFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

/-- Witness-only observation of clean real context data. No compiler or source
acceptance check is added. -/
def cleanB (ctx : Ctx) : Bool := ctx.insts.all fun info =>
  decide (info.data.regsIn = [] ∧ covV info.data = true)

def recordB (event : BlockScanEvent) (record : ScanRecord) : Bool :=
  record.inst == 0 && cleanB event.ctx &&
  decide ((event.ctx.insts[record.inst]?).map (fun info => (info.clif,info.results)) =
    some (some (.iconst .i64 9),[7])) &&
  record.output.step.any (fun step => step.decision == .emitted && step.results.any (fun rs => !rs.isEmpty)) &&
  record.output.emitted.any (fun i => !i.isCtl)

/-- The actual source returns a register, binds and retains a nonempty emitted
ordinary record, with clean context data. Full checked/physical stages are
reused from the complete cached emission fixture in downstream witnesses. -/
def Observed : Prop := (Stock.lower (function false)).toOption.map (fun result => decide (
  (Stock.runTerm result.ctx "lower" [.inst 0] result.initial).toOption.any
    (fun (out,_,_) => out.any (fun v => !v.regsIn.isEmpty)) = true ∧
  (emitInstruction result.ctx 0 result.initial).toOption.any (fun emission => !emission.code.isEmpty) = true ∧
  result.blockScans.any (fun event => event.output.records.any (recordB event)) = true)) = some true

/-- Cached kernel evidence for the real nonempty result, binding and retained
record of the same complete original source used by the generic witnesses. -/
theorem stock_binding_observed : Observed := by unfold Observed; decide +kernel

end Backend.Stock.Proof.BindingCoverageWitness
