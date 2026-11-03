import FV.Backend.Proof.StockAcquireWholePendingSourceOrder

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- An internal actual frontier retains the interpreter obligation for every emitted decision. -/
def ExecutedRecordFrontier (f : Clif.Function) (ctx : Ctx) (record : ScanRecord) (pending : List Nat) : Prop :=
  RecordFrontier f ctx record pending ∧
    ∀ step,record.output.step = some step → step.decision = .emitted →
      ReadPendingMarks ctx (scanState record.input record.inst) pending record.output.state

/-- Actual named execution supplies the stronger frontier without changing any accepted input. -/
theorem stock_lower_record_executed_frontier {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records) :
    ∃ pending,ExecutedRecordFrontier f event.ctx record pending := by
  by_cases emitting : ∃ step,record.output.step = some step ∧ step.decision = .emitted
  · obtain ⟨step,recorded,emitted⟩ := emitting
    obtain ⟨pending,trace,exactSunk,frames⟩ := stock_lower_record_read_pending_marks run events records recorded emitted
    obtain ⟨original,ranges,initial,built,func,table⟩ := stock_lower_record_color_events run events records
    have metadata : (scanState record.input record.inst).entryColor = (sourceMetadata original ranges).entryColor :=
      (scanState_entry_colors _ _).trans (table.trans (sourceMetadata_color_events original ranges).symm)
    refine ⟨pending,⟨exactSunk,?_,Or.inl ⟨step,recorded,emitted,trace.forget⟩⟩,?_⟩
    · intro producer member
      exact ⟨original,ranges,initial,built,trace.forget.forget.source_members built metadata producer member⟩
    · intro actual actualRecorded actualEmitted
      exact trace
  · obtain ⟨pending,frontier⟩ := stock_lower_record_frontier run events records
    have empty : pending = [] := by
      rcases frontier.2.2 with ⟨step,recorded,emitted,trace⟩ | ⟨empty,same⟩
      · exact False.elim (emitting ⟨step,recorded,emitted⟩)
      · exact empty
    refine ⟨pending,frontier,?_⟩
    intro step recorded emitted
    exact False.elim (emitting ⟨step,recorded,emitted⟩)

end Backend.Stock.Proof.Acquire810
