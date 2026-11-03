import FV.Backend.Proof.StockAcquireSourceColorGap

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual record decisions preserve the internally derived source interval without hidden block boundaries. -/
theorem stock_lower_record_source_color_gap {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {original : Ctx} {ranges : Array (Nat × Nat)} {initial : LState}
    (built : Backend.buildCtx f = .ok (original,ranges,initial))
    (metadata : record.input.entryColor = (sourceMetadata original ranges).entryColor)
    {cut : Nat} (covered : SourceColorGap original ranges cut record.input)
    (sunkCut : record.input.sunk[record.inst]! = true →
      referenceCut record.input.entryColor cut record.inst ≤ cut) :
    SourceColorGap original ranges (referenceCut record.input.entryColor cut record.inst) record.output.state := by
  by_cases emitting : ∃ step,record.output.step = some step ∧ step.decision = .emitted
  · obtain ⟨step,recorded,emitted⟩ := emitting
    obtain ⟨pending,reads,exactSunk,frames⟩ := stock_lower_record_read_pending_marks run events records recorded emitted
    have scannedMeta := (scanState_entry_colors record.input record.inst).trans metadata
    by_cases zero : record.input.entryColor[record.inst]! = 0
    · have normalized := covered.of_color_eq (scanState_color_zero record.input record.inst zero)
      have after := SourceColorGap.append_execution built scannedMeta normalized reads.forget.forget
      simpa only [referenceCut,zero,ite_true] using after
    · have after := SourceColorGap.reset_execution built scannedMeta
        (scanState_color_positive record.input record.inst zero) reads.forget.forget
      simpa only [referenceCut,zero,ite_false] using after
  · have actual := ScansSpec.record_run (runScans_spec (stock_lower_event_scan_run run events)) record records
    cases sunk : record.input.sunk[record.inst]! with
    | true =>
      have same := Except.ok.inj (actual.symm.trans (scan_sunk event.ctx event.block record.inst event.termInst event.isBranch record.input sunk))
      have colorEq := congrArg (fun scan : Scan => scan.state.color) same
      exact (covered.shrink (sunkCut sunk)).of_color_eq colorEq
    | false =>
      have colorEq := scan_no_emission_color sunk actual (fun step recorded emitted => emitting ⟨step,recorded,emitted⟩)
      by_cases zero : record.input.entryColor[record.inst]! = 0
      · have after := covered.of_color_eq (colorEq.trans (scanState_color_zero record.input record.inst zero))
        simpa only [referenceCut,zero,ite_true] using after
      · have after : SourceColorGap original ranges record.input.entryColor[record.inst]! record.output.state :=
          SourceColorGap.at_color (colorEq.trans (scanState_color_positive record.input record.inst zero))
        simpa only [referenceCut,zero,ite_false] using after

end Backend.Stock.Proof.Acquire810
