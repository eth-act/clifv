import FV.Backend.Proof.StockAcquireSunkFrontierStep

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Every actual emitted record derives its own absent sunk flag. -/
theorem stock_lower_emitted_record_unsunk {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    record.input.sunk[record.inst]! = false := by
  have actual := ScansSpec.record_run (runScans_spec (stock_lower_event_scan_run run events)) record records
  cases marked : record.input.sunk[record.inst]! with
  | false => rfl
  | true =>
    have outputEq := Except.ok.inj (actual.symm.trans (scan_sunk event.ctx event.block record.inst event.termInst event.isBranch record.input marked))
    rw [outputEq] at recorded
    have equal := Option.some.inj recorded.symm
    have wrong := congrArg Step.decision equal
    rw [emitted] at wrong
    cases wrong

/-- The exact retained source prefix derives its selected capture and queue head internally. -/
theorem stock_lower_acquire_actual_prefix_head {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record)
    {env : Clif.Env} {program : Clif.Program} {before after : Clif.Frame × Clif.Mem}
    (frontier : ReadEffectFrontier event.ctx env program)
    (history : SourceReadCaptures event.ctx env program (event.output.records.reverse.take R.consumerIndex) before after frontier.history)
    (marked : PendingReadMarks frontier record.output.state) (retired : RetiredReadUnmarked frontier record.output.state) :
    ∃ captured remaining,frontier.pending = captured::remaining ∧ captured.record.inst = R.producer := by
  have sourceMember : R.producer ∈ List.range' (blockStart f event.block) R.consumerIndex := by
    apply List.mem_range'.mpr
    exact ⟨R.producerIndex,R.before,by simpa only [Nat.one_mul] using R.position⟩
  rw [← stock_lower_acquire_source_prefix_indices run scope events R] at sourceMember
  obtain ⟨producerRecord,inPrefix,position⟩ := List.mem_map.mp sourceMember
  have retained : producerRecord ∈ event.output.records := List.mem_reverse.mp (List.mem_of_mem_take inPrefix)
  have producerBefore : producerRecord.inst < record.inst := by rw [position,R.position,R.current];exact Nat.add_lt_add_left R.before _
  have producerMarked := stock_lower_record_mark_propagates run events records retained producerBefore
    (stock_lower_acquire_output_producer_marked run scope events records recorded emitted selectedId R)
  have slotMember : R.producer ∈
      ((event.output.records.reverse.take R.consumerIndex).filter (fun actual => actual.input.sunk[actual.inst]!)).map (·.inst) := by
    apply List.mem_map.mpr
    exact ⟨producerRecord,List.mem_filter.mpr ⟨inPrefix,by simpa only [position] using producerMarked⟩,position⟩
  rw [← history.marked_slots] at slotMember
  obtain ⟨captured,member,producer⟩ := List.mem_map.mp slotMember
  have reverseOrder := stock_lower_event_records_reverse_order run events
  have forwardOrder : event.output.records.reverse.Pairwise (fun first second => first.inst < second.inst) :=
    List.pairwise_reverse.mpr reverseOrder
  have prefixOrder := forwardOrder.sublist (List.take_sublist R.consumerIndex event.output.records.reverse)
  have historyOrder : (frontier.history.map (fun actual => actual.record.inst)).Pairwise (· < ·) := by
    rw [history.marked_slots]
    apply List.pairwise_map.mpr
    exact prefixOrder.sublist List.filter_sublist
  have allRetained : ∀ actual ∈ frontier.history,actual.record ∈ event.output.records := by
    intro actual present
    exact List.mem_reverse.mp (List.mem_of_mem_take (history.record_membership actual present))
  obtain ⟨remaining,head⟩ := stock_lower_acquire_captured_pending_head run scope events records recorded emitted selectedId R
    allRetained historyOrder member producer marked retired
  exact ⟨captured,remaining,head,producer⟩

end Backend.Stock.Proof.Acquire810
