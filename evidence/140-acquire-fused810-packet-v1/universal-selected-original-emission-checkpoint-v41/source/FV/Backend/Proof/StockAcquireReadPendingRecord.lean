import FV.Backend.Proof.StockAcquireReadPendingNamed
import FV.Backend.Proof.StockAcquireRecordSourceInterval

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Every actual emitted record derives its complete classified read frontier through result binding. -/
theorem stock_lower_record_read_pending_marks {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ pending,ReadPendingMarks event.ctx (scanState record.input record.inst) pending record.output.state ∧
      record.output.state.sunk = pending.foldl (fun bits producer => bits.set! producer true) record.input.sunk ∧
      ∀ producer ∈ pending,SourceReadFrame event.ctx producer := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  obtain ⟨pending,reads⟩ := stock_lower_helper_read_pending
    (stock_lower_sink_format_sources run event events) receipt.rootRun
  obtain ⟨entries,color,sunk⟩ := bindResults_mark_fields receipt.binding
  have binding : ReadPendingMarks event.ctx receipt.next [] receipt.bound :=
    .frame entries color sunk (.nil receipt.bound)
  have complete := reads.append binding
  simp only [List.append_nil] at complete
  rw [← receipt.state] at complete
  have exactSunk := complete.forget.sunk_exact
  rw [scanState_sunk] at exactSunk
  exact ⟨pending,complete,exactSunk,complete.source_memory⟩

/-- Every actual emitted read frontier derives its original source-event interval and source memory frames. -/
theorem stock_lower_record_read_pending_interval {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ pending,ReadPendingMarks event.ctx (scanState record.input record.inst) pending record.output.state ∧
      record.output.state.sunk = pending.foldl (fun bits producer => bits.set! producer true) record.input.sunk ∧
      (∀ producer ∈ pending,SourceReadFrame event.ctx producer) ∧
      (pending = [] ∨ ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState) (final : Nat),
        Backend.buildCtx f = .ok (original,ranges,initial) ∧ record.output.state.color = some final ∧
        ∀ pre producer post,pending = pre++producer::post →
          (sourceColorEvents original ranges)[final+post.length]? = some (some producer)) := by
  obtain ⟨pending,reads,exactSunk,frames⟩ := stock_lower_record_read_pending_marks run events records recorded emitted
  refine ⟨pending,reads,exactSunk,frames,?_⟩
  by_cases empty : pending = []
  · exact Or.inl empty
  obtain ⟨final,color⟩ := reads.forget.nonempty_color_some empty
  obtain ⟨original,ranges,initial,built,func,table⟩ := stock_lower_record_color_events run events records
  have metadata : record.input.entryColor = (sourceMetadata original ranges).entryColor :=
    table.trans (sourceMetadata_color_events original ranges).symm
  have scanned : (scanState record.input record.inst).entryColor =
      (sourceMetadata original ranges).entryColor := by
    unfold scanState
    dsimp only
    split <;> exact metadata
  refine Or.inr ⟨original,ranges,initial,final,built,color,?_⟩
  intro pre producer post splitList
  exact reads.forget.source_event_at_split built scanned color pre producer post splitList

end Backend.Stock.Proof.Acquire810
