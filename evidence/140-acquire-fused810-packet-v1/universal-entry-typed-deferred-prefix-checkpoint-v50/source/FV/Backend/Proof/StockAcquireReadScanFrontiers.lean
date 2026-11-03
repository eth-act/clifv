import FV.Backend.Proof.StockAcquireReadPendingRecord
import FV.Backend.Proof.StockAcquireForwardFrontiers

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual records derive their original frontier and every successful source read frame. -/
theorem stock_lower_record_read_frontier {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records) :
    ∃ pending,RecordFrontier f event.ctx record pending ∧
      ∀ producer ∈ pending,SourceReadFrame event.ctx producer := by
  by_cases emitting : ∃ step,record.output.step = some step ∧ step.decision = .emitted
  · obtain ⟨step,recorded,emitted⟩ := emitting
    obtain ⟨pending,reads,exactSunk,frames⟩ := stock_lower_record_read_pending_marks run events records recorded emitted
    obtain ⟨original,ranges,initial,built,func,table⟩ := stock_lower_record_color_events run events records
    have metadata : record.input.entryColor = (sourceMetadata original ranges).entryColor :=
      table.trans (sourceMetadata_color_events original ranges).symm
    have scanned : (scanState record.input record.inst).entryColor =
        (sourceMetadata original ranges).entryColor := by
      unfold scanState
      dsimp only
      split <;> exact metadata
    refine ⟨pending,⟨exactSunk,?_,Or.inl ⟨step,recorded,emitted,reads.forget⟩⟩,frames⟩
    intro producer member
    exact ⟨original,ranges,initial,built,reads.forget.forget.source_members built scanned producer member⟩
  · obtain ⟨pending,frontier⟩ := stock_lower_record_frontier run events records
    refine ⟨pending,frontier,?_⟩
    rcases frontier.2.2 with ⟨step,recorded,emitted,marks⟩ | ⟨empty,unchanged⟩
    · exact False.elim (emitting ⟨step,recorded,emitted⟩)
    · rw [empty]
      simp

private theorem scans_read_frontiers {f : Clif.Function} {ctx : Ctx}
    {exec : Nat → State → Except String Scan} {indices : List Nat} {before : State} {output : BlockScan}
    (spec : ScansSpec exec indices before output)
    (localFrontier : ∀ record ∈ output.records,∃ pending,RecordFrontier f ctx record pending ∧
      ∀ producer ∈ pending,SourceReadFrame ctx producer) :
    ∃ groups : List (List Nat),RecordFrontiers f ctx output.records groups ∧
      output.state.sunk = groups.flatten.foldl (fun bits producer => bits.set! producer true) before.sunk ∧
      ∀ producer ∈ groups.flatten,SourceReadFrame ctx producer := by
  revert localFrontier
  induction spec with
  | nil input => intro localFrontier; exact ⟨[],.nil,rfl,by simp⟩
  | @cons inst indices before scan tail head rest ih =>
    intro localFrontier
    obtain ⟨pending,front,headFrames⟩ := localFrontier _ (List.mem_cons_self ..)
    obtain ⟨groups,frontiers,exactSunk,tailFrames⟩ := ih (fun record member =>
      localFrontier record (List.mem_cons_of_mem _ member))
    refine ⟨pending::groups,.cons front frontiers,?_,?_⟩
    · simp only [List.flatten_cons,List.foldl_append]
      rw [← front.1]
      exact exactSunk
    · intro producer member
      rcases List.mem_append.mp member with member | member
      · exact headFrames producer member
      · exact tailFrames producer member

/-- Complete actual scans derive forward record association and all successful source read frames. -/
theorem stock_lower_event_read_frontiers {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) :
    ∃ groups : List (List Nat),RecordFrontiers f event.ctx event.output.records groups ∧
      RecordFrontiers f event.ctx event.output.records.reverse groups.reverse ∧
      event.output.state.sunk = groups.flatten.foldl (fun bits producer => bits.set! producer true) event.input.sunk ∧
      (∀ producer ∈ groups.reverse.flatten,SourceReadFrame event.ctx producer) ∧
      event.output.code.toList = event.output.records.reverse.flatMap (fun record => record.output.emitted.toList) := by
  obtain ⟨groups,frontiers,exactSunk,frames⟩ := scans_read_frontiers
    (runScans_spec (stock_lower_event_scan_run run events))
    (fun record records => stock_lower_record_read_frontier run events records)
  refine ⟨groups,frontiers,frontiers.reverse,exactSunk,?_,scanBlock_forward_chunks (stock_lower_event_scan_run run events)⟩
  intro producer member
  obtain ⟨group,groupMember,producerMember⟩ := List.mem_flatten.mp member
  exact frames producer (List.mem_flatten.mpr ⟨group,List.mem_reverse.mp groupMember,producerMember⟩)

end Backend.Stock.Proof.Acquire810
