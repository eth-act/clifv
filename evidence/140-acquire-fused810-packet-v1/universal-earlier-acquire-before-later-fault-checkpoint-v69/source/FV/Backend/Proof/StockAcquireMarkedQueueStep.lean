import FV.Backend.Proof.StockAcquireActualPendingMarked

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Every group in an actual record frontier derives its mark bound from initialization and execution. -/
theorem stock_lower_record_frontier_pending_bounds {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {pending : List Nat} (frontier : RecordFrontier f event.ctx record pending) :
    ∀ producer ∈ pending,producer < record.input.sunk.size := by
  rcases frontier.2.2 with ⟨step,recorded,emitted,trace⟩ | ⟨empty,same⟩
  · intro producer member
    have positive := trace.member_positive member
    have scanned : (scanState record.input record.inst).entryColor = record.input.entryColor := scanState_entry_colors _ _
    rw [scanned] at positive
    rw [stock_lower_record_sunk_color_extent run events records]
    apply Classical.byContradiction
    intro outside
    have absent := Array.getElem?_eq_none (Nat.le_of_not_lt outside)
    simp only [getElem!_def,absent] at positive
    exact positive rfl
  · subst pending
    simp

/-- A real record propagates the covered read queue together with every actual sunk mark. -/
theorem stock_lower_record_marked_read_queue_step {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {original : Ctx} {ranges : Array (Nat × Nat)} {initial : LState}
    (built : Backend.buildCtx f = .ok (original,ranges,initial))
    (metadata : record.input.entryColor = (sourceMetadata original ranges).entryColor)
    {cut : Nat} {queue : List Nat} (covered : ReadQueueCut event.ctx original ranges cut record.input queue)
    (marked : ∀ producer ∈ queue,record.input.sunk[producer]! = true)
    (sunkCut : record.input.sunk[record.inst]! = true → referenceCut record.input.entryColor cut record.inst ≤ cut) :
    ∃ pending,RecordFrontier f event.ctx record pending ∧
      ReadQueueCut event.ctx original ranges (referenceCut record.input.entryColor cut record.inst)
        record.output.state (queue++pending) ∧
      ∀ producer ∈ queue++pending,record.output.state.sunk[producer]! = true := by
  obtain ⟨pending,frontier,after⟩ := stock_lower_record_read_queue_step run events records built metadata covered sunkCut
  exact ⟨pending,frontier,after,frontier.queue_marks marked
    (stock_lower_record_frontier_pending_bounds run events records frontier)⟩

end Backend.Stock.Proof.Acquire810
