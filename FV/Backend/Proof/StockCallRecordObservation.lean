import FV.Backend.Proof.StockCallStaticSource
namespace Backend.Stock.Proof.CallRecordFixture
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open CallStaticFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

def callRecord (indirect implicit : Bool) (event : BlockScanEvent) (record : ScanRecord) : Bool :=
  match event.ctx.insts[record.inst]?,record.output.step with
  | some info,some step =>
    info.clif == some (callStatement indirect implicit).inst && step.decision == .emitted
  | _,_ => false

def Observed (indirect implicit : Bool) : Prop :=
  (Stock.lower (function indirect implicit)).toOption.map (fun result =>
    result.blockScans.toList.any (fun event => event.output.records.any (callRecord indirect implicit event))) = some true

/-- Actual direct/indirect ordinary and sret call sources have a real retained emitted call
record. This caches only the new record fact; earlier full pipeline evidence
is reused separately, without rerunning its allocator/physical/helper stages. -/
theorem observed (indirect implicit : Bool) : Observed indirect implicit := by
  cases indirect <;> cases implicit <;> unfold Observed <;> decide +kernel
end Backend.Stock.Proof.CallRecordFixture
