import FV.Backend.Proof.StockAcquirePendingSourcePositions

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual emitted records derive the exact original source-event interval of every pending group. -/
theorem stock_lower_record_pending_source_interval {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ pending,PendingMarks event.ctx (scanState record.input record.inst) pending record.output.state ∧
      record.output.state.sunk = pending.foldl (fun bits producer => bits.set! producer true) record.input.sunk ∧
      (pending = [] ∨ ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState) (final : Nat),
        Backend.buildCtx f = .ok (original,ranges,initial) ∧ record.output.state.color = some final ∧
        ∀ pre producer post,pending = pre++producer::post →
          (sourceColorEvents original ranges)[final+post.length]? = some (some producer)) := by
  obtain ⟨pending,marks,exactSunk,monotone⟩ := stock_lower_record_pending_marks run events records recorded emitted
  refine ⟨pending,marks,exactSunk,?_⟩
  by_cases empty : pending = []
  · exact Or.inl empty
  obtain ⟨final,color⟩ := marks.nonempty_color_some empty
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
  exact marks.source_event_at_split built scanned color pre producer post splitList

end Backend.Stock.Proof.Acquire810
