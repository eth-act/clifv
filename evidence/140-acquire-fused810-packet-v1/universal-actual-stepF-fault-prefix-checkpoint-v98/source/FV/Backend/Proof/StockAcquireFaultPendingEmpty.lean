import FV.Backend.Proof.StockAcquireReadBeforeLaterFault

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The actual successful prefix ends before the faulting producer.
Compiler marks then exclude every outstanding successful capture at that producer's selected consumer. -/
theorem stock_lower_acquire_fault_pending_empty {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record)
    {env : Clif.Env} {program : Clif.Program} {entry atFault : Clif.Frame × Clif.Mem}
    {frontier : ReadEffectFrontier event.ctx env program}
    (history : SourceReadCaptures event.ctx env program (event.output.records.reverse.take R.producerIndex) entry atFault frontier.history)
    (pending : PendingReadMarks frontier record.output.state) : frontier.pending = [] := by
  obtain ⟨block,blockAt,indices⟩ := stock_lower_event_forward_source_indices run scope events
  have blockEq := Option.some.inj (blockAt.symm.trans R.blockAt)
  subst block
  have inside := (List.getElem?_eq_some_iff.mp R.producerAt).1
  have prefixIndices : (event.output.records.reverse.take R.producerIndex).map (·.inst) =
      List.range' (blockStart f event.block) R.producerIndex := by
    rw [List.map_take,indices]
    exact List.take_range'_of_length_ge (by omega)
  cases pendingEq : frontier.pending with
  | nil => rfl
  | cons captured remaining =>
    have pendingMember : captured ∈ frontier.pending := by rw [pendingEq];exact List.mem_cons_self ..
    have historyMember : captured ∈ frontier.history := by rw [frontier.split];exact List.mem_append_right _ pendingMember
    have prefixMember := history.record_membership captured historyMember
    have retained := List.mem_reverse.mp (List.mem_of_mem_take prefixMember)
    have lower := stock_lower_acquire_marked_capture_order run scope events records recorded emitted selectedId R
      captured retained (pending captured pendingMember)
    have slotMember : captured.record.inst ∈ (event.output.records.reverse.take R.producerIndex).map (·.inst) :=
      List.mem_map.mpr ⟨captured.record,prefixMember,rfl⟩
    rw [prefixIndices] at slotMember
    obtain ⟨offset,bound,position⟩ := List.mem_range'.mp slotMember
    simp only [Nat.one_mul] at position
    have producer := R.position
    omega

/-- Actual source history and compiler marks recover every demanded binding at the selected fault boundary.
The proof derives the empty outstanding frontier; the caller supplies no completion certificate. -/
theorem stock_lower_acquire_fault_guarded_recovery {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record)
    {env : Clif.Env} {program : Clif.Program} {entry atFault : Clif.Frame × Clif.Mem} {MR : MemRelT}
    {frontier : ReadEffectFrontier event.ctx env program} {regs : Nat → CV} {world : Arm.ArmState}
    (history : SourceReadCaptures event.ctx env program (event.output.records.reverse.take R.producerIndex) entry atFault frontier.history)
    (pending : PendingReadMarks frontier record.output.state) (retired : RetiredUndemanded frontier record.output.state)
    (prior : PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history record.output.state
      (R.producerIndex,atFault) regs world) :
    GuardedScanRel f result event.ctx event.block MR record.output.state (R.producerIndex,atFault) regs world := by
  exact frontier_final_guarded prior retired
    (stock_lower_acquire_fault_pending_empty run scope events records recorded emitted selectedId R history pending)

end Backend.Stock.Proof.Acquire810
