import FV.Backend.Proof.StockAcquireRecordFrontier

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private theorem scans_frontiers {f : Clif.Function} {ctx : Ctx}
    {exec : Nat → State → Except String Scan} {indices : List Nat} {before : State} {output : BlockScan}
    (spec : ScansSpec exec indices before output)
    (localFrontier : ∀ record ∈ output.records,∃ pending,RecordFrontier f ctx record pending) :
    ∃ groups : List (List Nat), List.Forall₂ (RecordFrontier f ctx) output.records groups ∧
      output.state.sunk = groups.flatten.foldl (fun bits producer => bits.set! producer true) before.sunk := by
  revert localFrontier
  induction spec with
  | nil input => intro localFrontier; exact ⟨[],.nil,rfl⟩
  | @cons inst indices before scan tail head rest ih =>
    intro localFrontier
    obtain ⟨pending,front⟩ := localFrontier _ (List.mem_cons_self ..)
    obtain ⟨groups,frontiers,exactSunk⟩ := ih (fun record member =>
      localFrontier record (List.mem_cons_of_mem _ member))
    refine ⟨pending::groups,.cons front frontiers,?_⟩
    simp only [List.flatten_cons,List.foldl_append]
    rw [← front.1]
    exact exactSunk

/-- Actual whole scans retain each pending interpreter frontier beside its exact emitted record. -/
theorem stock_lower_event_record_frontiers {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) :
    ∃ groups : List (List Nat), List.Forall₂ (RecordFrontier f event.ctx) event.output.records groups ∧
      event.output.state.sunk = groups.flatten.foldl (fun bits producer => bits.set! producer true) event.input.sunk ∧
      event.output.code.toList = event.output.records.reverse.flatMap (fun record => record.output.emitted.toList) := by
  obtain ⟨groups,frontiers,exactSunk⟩ := scans_frontiers
    (runScans_spec (stock_lower_event_scan_run run events))
    (fun record records => stock_lower_record_frontier run events records)
  exact ⟨groups,frontiers,exactSunk,scanBlock_forward_chunks (stock_lower_event_scan_run run events)⟩

end Backend.Stock.Proof.Acquire810
