import FV.Backend.Proof.StockAcquirePendingSourceOrder
import FV.Backend.Proof.StockAcquireSelectedPending

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Every actual emitted record derives its general pending list and original source membership. -/
theorem stock_lower_record_pending_source_members {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState), ∃ pending out next fired,
      Backend.buildCtx f = .ok (original,ranges,initial) ∧ original.func = f ∧
      Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
        .ok (some out,next,fired) ∧
      PendingSinks event.ctx (scanState record.input record.inst) pending next ∧
      ∀ producer ∈ pending, some producer ∈ sourceColorEvents original ranges := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  obtain ⟨pending,actual⟩ := stock_runTerm_pending_execution receipt.rootRun
  obtain ⟨original,ranges,initial,built,func,table⟩ := stock_lower_record_color_events run events records
  have metadata : record.input.entryColor = (sourceMetadata original ranges).entryColor :=
    table.trans (sourceMetadata_color_events original ranges).symm
  have scanned : (scanState record.input record.inst).entryColor =
      (sourceMetadata original ranges).entryColor := by
    unfold scanState
    dsimp only
    split <;> exact metadata
  exact ⟨original,ranges,initial,pending,receipt.out,receipt.next,receipt.fired,
    built,func,receipt.rootRun,actual,actual.source_members built scanned⟩

/-- Real root810 records derive reverse source order without an external pending certificate. -/
theorem stock_lower_acquire_selected_source_order {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState), ∃ pending out next fired final,
      Backend.buildCtx f = .ok (original,ranges,initial) ∧ original.func = f ∧
      Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
        .ok (some out,next,fired) ∧
      PendingSinks event.ctx (scanState record.input record.inst) pending next ∧
      next.color = some final ∧ pending.Pairwise (fun first second => second < first) ∧
      ∀ producer ∈ pending, some producer ∈ sourceColorEvents original ranges := by
  obtain ⟨pending,out,next,fired,final,root,actual,finalColor,_,_,_⟩ :=
    stock_lower_acquire_selected_pending run scope events records recorded emitted selectedId
  obtain ⟨original,ranges,initial,built,func,table⟩ := stock_lower_record_color_events run events records
  have metadata : record.input.entryColor = (sourceMetadata original ranges).entryColor :=
    table.trans (sourceMetadata_color_events original ranges).symm
  have scanned : (scanState record.input record.inst).entryColor =
      (sourceMetadata original ranges).entryColor := by
    unfold scanState
    dsimp only
    split <;> exact metadata
  exact ⟨original,ranges,initial,pending,out,next,fired,final,built,func,root,actual,finalColor,
    actual.source_order built scanned finalColor,actual.source_members built scanned⟩

end Backend.Stock.Proof.Acquire810
