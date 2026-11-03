import FV.Backend.Proof.StockAcquireForwardFrontiers

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Successful sink execution retains an initialized source-color frontier. -/
theorem PendingMarks.color_some {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : PendingMarks ctx before pending after) {start : Nat} (color : before.color = some start) :
    ∃ final,after.color = some final := by
  revert start
  induction trace with
  | nil => intro start color; exact ⟨start,color⟩
  | sink actual tail ih =>
    intro start color
    apply ih
    rw [(sink_accepted actual).2.2.2.2]
  | frame entries unchanged sunk tail ih =>
    intro start color
    exact ih (unchanged.trans color)

/-- Any nonempty actual deferred frontier derives its final color internally. -/
theorem PendingMarks.nonempty_color_some {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : PendingMarks ctx before pending after) (nonempty : pending ≠ []) :
    ∃ final,after.color = some final := by
  induction trace with
  | nil => exact False.elim (nonempty rfl)
  | sink actual tail ih =>
    apply tail.color_some
    rw [(sink_accepted actual).2.2.2.2]
  | frame entries unchanged sunk tail ih => exact ih nonempty

/-- Every actual emitted record derives strict reverse source order for its complete pending list. -/
theorem stock_lower_record_pending_marks_order {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ pending, PendingMarks event.ctx (scanState record.input record.inst) pending record.output.state ∧
      record.output.state.sunk = pending.foldl (fun bits producer => bits.set! producer true) record.input.sunk ∧
      pending.Pairwise (fun first second => second < first) := by
  obtain ⟨pending,marks,exactSunk,monotone⟩ := stock_lower_record_pending_marks run events records recorded emitted
  refine ⟨pending,marks,exactSunk,?_⟩
  by_cases empty : pending = []
  · rw [empty]; exact .nil
  obtain ⟨final,color⟩ := marks.nonempty_color_some empty
  obtain ⟨original,ranges,initial,built,func,table⟩ := stock_lower_record_color_events run events records
  have metadata : record.input.entryColor = (sourceMetadata original ranges).entryColor :=
    table.trans (sourceMetadata_color_events original ranges).symm
  have scanned : (scanState record.input record.inst).entryColor =
      (sourceMetadata original ranges).entryColor := by
    unfold scanState
    dsimp only
    split <;> exact metadata
  exact marks.forget.source_order built scanned color

end Backend.Stock.Proof.Acquire810
