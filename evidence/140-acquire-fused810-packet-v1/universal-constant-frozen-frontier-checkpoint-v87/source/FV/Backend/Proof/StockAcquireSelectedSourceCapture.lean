import FV.Backend.Proof.StockAcquireActualProducerRecord

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The selected producer belongs to the actual forward source prefix and its exact successful capture history.
The prefix comes from the real scan suffix. No caller producer-position or capture-membership certificate is used. -/
theorem stock_lower_acquire_selected_source_capture {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record) :
    ∃ (earlier : List ScanRecord) (suffixIndices : List Nat) (tail : BlockScan),
      event.output.records = earlier++record::tail.records ∧
      ScansSpec (fun inst state => scanInstruction event.ctx event.block inst event.termInst event.isBranch state)
        suffixIndices record.output.state tail ∧
      ∀ (env : Clif.Env) (program : Clif.Program) (before after : Clif.Frame × Clif.Mem)
        (captures : List (SunkReadSnapshot event.ctx env program)),
        SourceReadCaptures event.ctx env program tail.records.reverse before after captures →
        ∃ captured ∈ captures,captured.record.inst = R.producer ∧ captured.record ∈ event.output.records := by
  have actual := runScans_spec (stock_lower_event_scan_run run events)
  obtain ⟨earlier,suffixIndices,tail,parts,suffixRun⟩ := ScansSpec.record_suffix actual records
  obtain ⟨producerRecord,retained,position,marked⟩ := stock_lower_acquire_actual_producer_record run scope events records recorded emitted selectedId R
  have order : producerRecord.inst < record.inst := by
    rw [position,R.position,R.current]
    exact Nat.add_lt_add_left R.before _
  have reverseOrder := stock_lower_event_records_reverse_order run events
  have producerIn := retained
  rw [parts] at producerIn reverseOrder
  have inTail : producerRecord ∈ tail.records := by
    rcases List.mem_append.mp producerIn with earlierMember | later
    · have backwards := (List.pairwise_append.mp reverseOrder).2.2 producerRecord earlierMember record (List.mem_cons_self ..)
      omega
    · rcases List.mem_cons.mp later with same | member
      · subst producerRecord
        omega
      · exact member
  refine ⟨earlier,suffixIndices,tail,parts,suffixRun,?_⟩
  intro env program before after captures trace
  have slotMember : R.producer ∈
      (tail.records.reverse.filter (fun actual => actual.input.sunk[actual.inst]!)).map (·.inst) := by
    apply List.mem_map.mpr
    exact ⟨producerRecord,List.mem_filter.mpr ⟨List.mem_reverse.mpr inTail,marked⟩,position⟩
  rw [← trace.marked_slots] at slotMember
  obtain ⟨captured,member,producerEq⟩ := List.mem_map.mp slotMember
  refine ⟨captured,member,producerEq,?_⟩
  have capturedRecord := trace.record_membership captured member
  have inSuffix := List.mem_reverse.mp capturedRecord
  rw [parts]
  exact List.mem_append_right _ (List.mem_cons_of_mem _ inSuffix)

end Backend.Stock.Proof.Acquire810
