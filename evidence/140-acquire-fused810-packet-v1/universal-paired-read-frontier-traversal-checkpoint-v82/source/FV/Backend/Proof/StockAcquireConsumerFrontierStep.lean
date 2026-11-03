import FV.Backend.Proof.StockAcquirePrefixHead

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The actual consumer derives its source prefix and queue head, executes its real chunk, and retires exactly that capture.
All source history, mark, memory, DFG and required-value fields advance together. No caller head certificate is used. -/
theorem stock_lower_acquire_consumer_frontier_step {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ R : SourceEndpointReceipt f event record,
      ∀ (env : Clif.Env) (program : Clif.Program) (entry before after : Clif.Frame × Clif.Mem),
      entry.1.body = R.block.body → SourceInstResult env program event.ctx record.inst before after →
      ∀ (F : BitVec 64 → Prop) (sb : Nat) (syms : String → Option Nat) (isem : Backend.Proof.Sem) (MR : MemRelT),
      MRStable F MR → MemRefines F sb syms isem → MemRelOk F sb syms f MR →
      ∀ (frontier : ReadEffectFrontier event.ctx env program) (regs : Nat → CV) (world : Arm.ArmState),
      SourceReadCaptures event.ctx env program (event.output.records.reverse.take R.consumerIndex) entry before frontier.history →
      PendingReadMarks frontier record.output.state → RetiredReadUnmarked frontier record.output.state →
      RetiredUndemanded frontier record.output.state →
      PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history record.output.state (R.consumerIndex,before) regs world →
      ∃ (next : ReadEffectFrontier event.ctx env program) (nextRegs : Nat → CV) (nextWorld : Arm.ArmState),
        seqRun isem (record.output.emitted.toList.map
          (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs world = some (.fall nextRegs nextWorld) ∧
        PendingGuardedScanRel f result event.ctx event.block env program MR next.history record.input (R.consumerIndex+1,after) nextRegs nextWorld ∧
        SourceReadCaptures event.ctx env program ((event.output.records.reverse.take R.consumerIndex)++[record]) entry after next.history ∧
        (∀ captured ∈ next.history,captured.record ∈ event.output.records) ∧
        PendingReadMarks next record.input ∧ RetiredReadUnmarked next record.input ∧ RetiredUndemanded next record.input := by
  obtain ⟨R,transfer⟩ := stock_lower_acquire_pending_consumer_transfer run scope dominated events records recorded emitted selectedId
  refine ⟨R,?_⟩
  intro env program entry before after body source F sb syms isem MR stable memorySem memoryOk
    frontier regs world history pending retiredMarks retiredValues related
  have steps := history.source_steps
  rw [stock_lower_acquire_source_prefix_indices run scope events R] at steps
  have retained : ∀ captured ∈ frontier.history,captured.record ∈ event.output.records := by
    intro captured member
    exact List.mem_reverse.mp (List.mem_of_mem_take (history.record_membership captured member))
  obtain ⟨nextRegs,nextWorld,executed,post⟩ := transfer env program entry before after body steps source
    F sb syms isem MR stable memorySem memoryOk frontier regs world retained pending retiredValues related
  obtain ⟨captured,remaining,head,producer⟩ := stock_lower_acquire_actual_prefix_head run scope events records recorded emitted selectedId R
    frontier history pending retiredMarks
  let next := frontier.retire captured remaining head
  have captureUnique := stock_lower_actual_prefix_capture_indices_nodup run events history
  rw [frontier.split,List.map_append,List.nodup_append] at captureUnique
  have pendingUnique := captureUnique.2.1
  have marksAfter := stock_lower_acquire_pending_marks_retire run scope events records recorded emitted selectedId R
    frontier captured remaining head producer pendingUnique pending
  have retiredMarksAfter := stock_lower_acquire_retired_marks run scope events records recorded emitted selectedId R
    frontier captured remaining head producer retiredMarks
  have retiredValuesAfter := stock_lower_acquire_retired_undemanded run scope dominated events records recorded emitted selectedId R
    frontier captured remaining head producer retiredValues
  have unmarked := stock_lower_emitted_record_unsunk run events records recorded emitted
  have single : SourceReadCaptures event.ctx env program [record] before after [] := .skipped unmarked source (.nil after)
  have historyAfter := SourceReadCaptures.append history single
  simp only [List.append_nil] at historyAfter
  exact ⟨next,nextRegs,nextWorld,executed,post,historyAfter,retained,marksAfter,retiredMarksAfter,retiredValuesAfter⟩

end Backend.Stock.Proof.Acquire810
