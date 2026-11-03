import FV.Backend.Proof.StockAcquireCapturedEntryMarks

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Any actual capture still marked at this consumer is this producer or a later original producer. -/
theorem stock_lower_acquire_marked_capture_order {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record)
    {env : Clif.Env} {program : Clif.Program} (captured : SunkReadSnapshot event.ctx env program)
    (retained : captured.record ∈ event.output.records)
    (marked : record.output.state.sunk[captured.record.inst]! = true) : R.producer ≤ captured.record.inst := by
  by_cases same : captured.record.inst = R.producer
  · rw [same]
    exact Nat.le_refl _
  · have delta := stock_lower_acquire_sunk_delta run scope events records recorded emitted selectedId R
    have inputMarked : record.input.sunk[captured.record.inst]! = true := by
      rw [delta,Array.getElem!_set!_ne _ _ _ _ (Ne.symm same)] at marked
      exact marked
    obtain ⟨groups,frontiers,exactMarks,order⟩ := stock_lower_event_executed_source_order run scope events
    have actual := runScans_spec (stock_lower_event_scan_run run events)
    obtain ⟨earlier,pending,later,parts,frontier,marks⟩ := ScansSpec.executed_record_group_prefix actual frontiers records
    have singleton := executed_frontier_acquire_singleton run scope events records recorded emitted selectedId R frontier
    rw [marks] at inputMarked
    rcases sunk_fold_marked event.input.sunk earlier.flatten captured.record.inst inputMarked with inherited | member
    · have absent := stock_lower_captured_entry_unmarked run scope events captured retained
      rw [absent] at inherited
      cases inherited
    · have present : R.producer ∈ pending := by rw [singleton];exact List.mem_singleton_self _
      rw [parts,List.flatten_append,List.flatten_cons] at order
      have before := (List.pairwise_append.mp order).2.2 captured.record.inst member R.producer (List.mem_append_left _ present)
      exact Nat.le_of_lt before

/-- Actual source order and compiler marks identify the selected captured queue head internally. -/
theorem stock_lower_acquire_captured_pending_head {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record)
    {env : Clif.Env} {program : Clif.Program} {frontier : ReadEffectFrontier event.ctx env program}
    {captured : SunkReadSnapshot event.ctx env program}
    (retained : ∀ actual ∈ frontier.history,actual.record ∈ event.output.records)
    (sourceOrder : (frontier.history.map (fun actual => actual.record.inst)).Pairwise (· < ·))
    (member : captured ∈ frontier.history) (producer : captured.record.inst = R.producer)
    (marked : PendingReadMarks frontier record.output.state) (retired : RetiredReadUnmarked frontier record.output.state) :
    ∃ tail,frontier.pending = captured::tail := by
  have pendingMember := stock_lower_acquire_selected_capture_pending run scope events records recorded emitted selectedId R member producer retired
  rw [frontier.split,List.map_append,List.pairwise_append] at sourceOrder
  have pendingOrder := sourceOrder.2.1
  cases pendingEq : frontier.pending with
  | nil => rw [pendingEq] at pendingMember;cases pendingMember
  | cons head tail =>
    rw [pendingEq] at pendingMember
    rcases List.mem_cons.mp pendingMember with same | later
    · subst head
      exact ⟨tail,rfl⟩
    · have headMember : head ∈ frontier.pending := by rw [pendingEq];exact List.mem_cons_self ..
      have headHistory : head ∈ frontier.history := by rw [frontier.split];exact List.mem_append_right _ headMember
      have bound := stock_lower_acquire_marked_capture_order run scope events records recorded emitted selectedId R head
        (retained head headHistory) (marked head headMember)
      rw [pendingEq,List.map_cons,List.pairwise_cons] at pendingOrder
      have smaller := pendingOrder.1 captured.record.inst (List.mem_map.mpr ⟨captured,later,rfl⟩)
      rw [producer] at smaller
      omega

/-- The actual selected scan suffix derives both capture membership and source order for the pending head. -/
theorem stock_lower_acquire_actual_capture_head {f : Clif.Function} {result : Result}
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
        (frontier : ReadEffectFrontier event.ctx env program),
        SourceReadCaptures event.ctx env program tail.records.reverse before after frontier.history →
        PendingReadMarks frontier record.output.state → RetiredReadUnmarked frontier record.output.state →
        ∃ captured remaining,frontier.pending = captured::remaining ∧ captured.record.inst = R.producer := by
  obtain ⟨earlier,suffixIndices,tail,parts,suffixRun,locate⟩ := stock_lower_acquire_selected_source_capture run scope events records recorded emitted selectedId R
  refine ⟨earlier,suffixIndices,tail,parts,suffixRun,?_⟩
  intro env program before after frontier trace marked retired
  obtain ⟨captured,member,producer,retained⟩ := locate env program before after frontier.history trace
  have recordOrder := stock_lower_event_records_reverse_order run events
  rw [parts,List.pairwise_append] at recordOrder
  have tailOrder := (List.pairwise_cons.mp recordOrder.2.1).2
  have forwardOrder : tail.records.reverse.Pairwise (fun first second => first.inst < second.inst) := List.pairwise_reverse.mpr tailOrder
  have historyOrder : (frontier.history.map (fun actual => actual.record.inst)).Pairwise (· < ·) := by
    rw [trace.marked_slots]
    apply List.pairwise_map.mpr
    exact forwardOrder.sublist List.filter_sublist
  have allRetained : ∀ actual ∈ frontier.history,actual.record ∈ event.output.records := by
    intro actual present
    have inTail := List.mem_reverse.mp (trace.record_membership actual present)
    rw [parts]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ inTail)
  obtain ⟨remaining,head⟩ := stock_lower_acquire_captured_pending_head run scope events records recorded emitted selectedId R
    allRetained historyOrder member producer marked retired
  exact ⟨captured,remaining,head,producer⟩

end Backend.Stock.Proof.Acquire810
