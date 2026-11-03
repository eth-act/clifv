import FV.Backend.Proof.StockAcquirePendingBindFrame
import FV.Backend.Proof.StockAcquireMetadataEvents
import FV.Backend.Proof.StockSelectionReceipts

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Real scan resets preserve every existing deferred mark. -/
theorem scanState_sunk (state : State) (inst : Nat) : (scanState state inst).sunk = state.sunk := by
  unfold scanState
  dsimp only
  split <;> rfl

/-- Every actual emitted record derives its complete sink updates through output binding. -/
theorem stock_lower_record_pending_marks {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ pending, PendingMarks event.ctx (scanState record.input record.inst) pending record.output.state ∧
      record.output.state.sunk = pending.foldl (fun bits producer => bits.set! producer true) record.input.sunk ∧
      ∀ (target : Nat),record.input.sunk[target]! = true → record.output.state.sunk[target]! = true := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  obtain ⟨pending,marks⟩ := stock_runTerm_pending_marks_execution receipt.rootRun
  obtain ⟨entries,color,sunk⟩ := bindResults_mark_fields receipt.binding
  have binding : PendingMarks event.ctx receipt.next [] receipt.bound :=
    .frame entries color sunk (.nil receipt.bound)
  have complete := marks.append binding
  simp only [List.append_nil] at complete
  rw [← receipt.state] at complete
  have exactSunk := complete.sunk_exact
  rw [scanState_sunk] at exactSunk
  refine ⟨pending,complete,exactSunk,?_⟩
  intro target marked
  apply complete.marked_mono target
  rwa [scanState_sunk]

/-- Complete real record updates retain membership in the original general source queue. -/
theorem stock_lower_record_pending_mark_sources {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState), ∃ pending,
      Backend.buildCtx f = .ok (original,ranges,initial) ∧ original.func = f ∧
      PendingMarks event.ctx (scanState record.input record.inst) pending record.output.state ∧
      record.output.state.sunk = pending.foldl (fun bits producer => bits.set! producer true) record.input.sunk ∧
      ∀ producer ∈ pending,some producer ∈ sourceColorEvents original ranges := by
  obtain ⟨pending,marks,exactSunk,monotone⟩ :=
    stock_lower_record_pending_marks run events records recorded emitted
  obtain ⟨original,ranges,initial,built,func,table⟩ := stock_lower_record_color_events run events records
  have metadata : record.input.entryColor = (sourceMetadata original ranges).entryColor :=
    table.trans (sourceMetadata_color_events original ranges).symm
  have scanned : (scanState record.input record.inst).entryColor =
      (sourceMetadata original ranges).entryColor := by
    unfold scanState
    dsimp only
    split <;> exact metadata
  exact ⟨original,ranges,initial,pending,built,func,marks,exactSunk,
    marks.forget.source_members built scanned⟩

end Backend.Stock.Proof.Acquire810
