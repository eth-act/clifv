import FV.Backend.Proof.StockAcquireInheritedBlockMarks

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The actual complete frontier derives the exact mark fold before any selected retained record. -/
theorem ScansSpec.executed_record_group_prefix {f : Clif.Function} {ctx : Ctx}
    {exec : Nat → State → Except String Scan} {indices : List Nat} {input : State} {output : BlockScan}
    (spec : ScansSpec exec indices input output) {groups : List (List Nat)}
    (frontiers : ExecutedRecordFrontiers f ctx output.records groups)
    {record : ScanRecord} (member : record ∈ output.records) :
    ∃ (earlier : List (List Nat)) (pending : List Nat) (later : List (List Nat)),
      groups = earlier++pending::later ∧ ExecutedRecordFrontier f ctx record pending ∧
      record.input.sunk = earlier.flatten.foldl (fun bits producer => bits.set! producer true) input.sunk := by
  induction spec generalizing groups with
  | nil input => cases member
  | @cons inst indices input scan tail head rest ih =>
    cases frontiers with
    | @cons actual pending actualRecords actualGroups currentFrontier tailFrontiers =>
      rcases List.mem_cons.mp member with same | later
      · subst record
        exact ⟨[],pending,actualGroups,rfl,currentFrontier,rfl⟩
      · obtain ⟨earlier,group,laterGroups,parts,frontier,marks⟩ := ih tailFrontiers later
        refine ⟨pending::earlier,group,laterGroups,?_,frontier,?_⟩
        · rw [parts]
          rfl
        · rw [List.flatten_cons,List.foldl_append,← currentFrontier.1.1]
          exact marks

/-- The selected sink cannot inherit its own mark from another group or block entry. -/
theorem stock_lower_acquire_consumer_input_unmarked {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record) :
    record.input.sunk[R.producer]! = false := by
  obtain ⟨groups,frontiers,exactMarks,order⟩ := stock_lower_event_executed_source_order run scope events
  have actual := runScans_spec (stock_lower_event_scan_run run events)
  obtain ⟨earlier,pending,later,parts,frontier,marks⟩ := ScansSpec.executed_record_group_prefix actual frontiers records
  have singleton := executed_frontier_acquire_singleton run scope events records recorded emitted selectedId R frontier
  have present : R.producer ∈ pending := by rw [singleton];exact List.mem_singleton_self _
  have absent : R.producer ∉ earlier.flatten := by
    intro member
    rw [parts,List.flatten_append,List.flatten_cons] at order
    have impossible := (List.pairwise_append.mp order).2.2 R.producer member R.producer (List.mem_append_left _ present)
    omega
  rw [marks,sunk_fold_absent _ _ _ absent]
  exact stock_lower_acquire_entry_producer_unsunk run scope events R

end Backend.Stock.Proof.Acquire810
