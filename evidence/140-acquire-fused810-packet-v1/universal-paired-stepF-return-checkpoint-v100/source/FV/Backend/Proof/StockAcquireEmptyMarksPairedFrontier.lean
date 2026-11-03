import FV.Backend.Proof.StockAcquirePairedReadFrontier

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- An actual emitted record with an empty sink group preserves the general outstanding queue.
The local semantic obligation retains every required binding in both worlds. -/
theorem stock_lower_empty_marks_paired_frontier_at {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (marks : PendingMarks event.ctx (scanState record.input record.inst) [] record.output.state)
    {env : Clif.Env} {program : Clif.Program} {MR : MemRelT} {Z : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    {entry : Clif.Frame × Clif.Mem} {prefixRecords : List ScanRecord} {before after : SourcePoint}
    (source : IndexedSourceInst env program f event.ctx event.block record.inst before after)
    {regs nextRegs : Nat → CV} {worlds nextWorlds : W2}
    (prior : PairedReadFrontierAt f result event env program MR Z entry prefixRecords record.output.state before regs worlds)
    (executed : seqRun (pairSem isem) (record.output.emitted.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs worlds = some (.fall nextRegs nextWorlds))
    (left : PendingGuardedScanRel f result event.ctx event.block env program MR prior.frontier.history record.input after nextRegs nextWorlds.1)
    (right : PendingGuardedScanRel f result event.ctx event.block env program MR prior.frontier.history record.input after nextRegs nextWorlds.2)
    (agreement : SameWorld Z nextWorlds.1 nextWorlds.2) :
    ∃ post : PairedReadFrontierAt f result event env program MR Z entry (prefixRecords++[record]) record.input after nextRegs nextWorlds,
      post.frontier = prior.frontier ∧
      seqRun (pairSem isem) (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs worlds = some (.fall nextRegs nextWorlds) := by
  have sunkEq : record.output.state.sunk = record.input.sunk := by
    simpa only [List.foldl_nil,scanState_sunk] using marks.sunk_exact
  have unmarked := stock_lower_emitted_record_unsunk run events records recorded emitted
  have one : SourceReadCaptures event.ctx env program [record] before.2 after.2 [] :=
    .skipped unmarked source.2.2 (.nil after.2)
  have history := SourceReadCaptures.append prior.history one
  simp only [List.append_nil] at history
  have pending : PendingReadMarks prior.frontier record.input := by
    intro captured member
    rw [← sunkEq]
    exact prior.pending captured member
  have retiredMarks : RetiredReadUnmarked prior.frontier record.input := by
    intro captured member
    rw [← sunkEq]
    exact prior.retiredMarks captured member
  have retiredValues := retired_undemanded_of_le prior.retiredValues
    (stock_lower_record_demand_mono run events records recorded emitted)
  exact ⟨⟨prior.frontier,history,prior.retained,pending,retiredMarks,retiredValues,left,right,agreement⟩,rfl,executed⟩

end Backend.Stock.Proof.Acquire810
