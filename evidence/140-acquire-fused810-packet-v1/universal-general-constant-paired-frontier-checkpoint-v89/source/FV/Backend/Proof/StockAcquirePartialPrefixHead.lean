import FV.Backend.Proof.StockAcquireFallbackFrozenStep

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A real source prefix can stop before the consumer, including immediately before a later source fault.
Actual scan indices, original marks and prefix execution derive the successful producer's pending-head position. -/
theorem stock_lower_acquire_partial_prefix_head {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record)
    {cut : Nat} (producerBefore : R.producerIndex < cut) (beforeConsumer : cut ≤ R.consumerIndex)
    {env : Clif.Env} {program : Clif.Program} {entry atFault : Clif.Frame × Clif.Mem}
    {frontier : ReadEffectFrontier event.ctx env program}
    (history : SourceReadCaptures event.ctx env program (event.output.records.reverse.take cut) entry atFault frontier.history)
    (pending : PendingReadMarks frontier record.output.state)
    (retired : RetiredReadUnmarked frontier record.output.state) :
    ∃ captured remaining,frontier.pending = captured::remaining ∧ captured.record.inst = R.producer ∧
      captured ∈ frontier.history ∧ captured.record ∈ event.output.records := by
  obtain ⟨block,blockAt,allIndices⟩ := stock_lower_event_forward_source_indices run scope events
  have blockEq := Option.some.inj (blockAt.symm.trans R.blockAt)
  subst block
  have consumerBound := (List.getElem?_eq_some_iff.mp R.consumerAt).1
  have prefixIndices : (event.output.records.reverse.take cut).map (·.inst) =
      List.range' (blockStart f event.block) cut := by
    rw [List.map_take,allIndices]
    exact List.take_range'_of_length_ge (by omega)
  have producerMember : R.producer ∈ (event.output.records.reverse.take cut).map (·.inst) := by
    rw [prefixIndices,List.mem_range']
    refine ⟨R.producerIndex,producerBefore,?_⟩
    simpa only [Nat.one_mul] using R.position
  obtain ⟨producerRecord,inPrefix,position⟩ := List.mem_map.mp producerMember
  have producerRetained := List.mem_reverse.mp (List.mem_of_mem_take inPrefix)
  have producerOrder : producerRecord.inst < record.inst := by
    rw [position,R.position,R.current]
    exact Nat.add_lt_add_left R.before _
  have marked := stock_lower_record_mark_propagates run events records producerRetained producerOrder
    (stock_lower_acquire_output_producer_marked run scope events records recorded emitted selectedId R)
  have ownMarked : producerRecord.input.sunk[producerRecord.inst]! = true := by rwa [position]
  have markedMember : R.producer ∈
      ((event.output.records.reverse.take cut).filter (fun actual => actual.input.sunk[actual.inst]!)).map (·.inst) := by
    exact List.mem_map.mpr ⟨producerRecord,List.mem_filter.mpr ⟨inPrefix,ownMarked⟩,position⟩
  rw [← history.marked_slots] at markedMember
  obtain ⟨captured,member,producerEq⟩ := List.mem_map.mp markedMember
  have retained : ∀ actual ∈ frontier.history,actual.record ∈ event.output.records := by
    intro actual present
    exact List.mem_reverse.mp (List.mem_of_mem_take (history.record_membership actual present))
  have forwardOrder : event.output.records.reverse.Pairwise (fun first second => first.inst < second.inst) :=
    List.pairwise_reverse.mpr (stock_lower_event_records_reverse_order run events)
  have sourceOrder : (frontier.history.map (fun actual => actual.record.inst)).Pairwise (· < ·) := by
    rw [history.marked_slots]
    exact List.pairwise_map.mpr ((forwardOrder.sublist (List.take_sublist cut _)).sublist List.filter_sublist)
  obtain ⟨remaining,head⟩ := stock_lower_acquire_captured_pending_head run scope events records recorded emitted selectedId R
    retained sourceOrder member producerEq pending retired
  exact ⟨captured,remaining,head,producerEq,member,retained captured member⟩

end Backend.Stock.Proof.Acquire810
