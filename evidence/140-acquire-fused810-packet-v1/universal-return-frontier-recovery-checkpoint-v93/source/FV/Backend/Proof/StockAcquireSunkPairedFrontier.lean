import FV.Backend.Proof.StockAcquireSourceCaptureAppend
import FV.E2E.Pair

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The real sunk callback extends source history and every pending invariant while its code remains empty.
This theorem covers successful reads. The separate first-fault snapshot branch remains unchanged. -/
theorem stock_lower_sunk_paired_frontier_step {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (marked : record.input.sunk[record.inst]! = true)
    {bi j : Nat} {block : Clif.Block} {stm : Clif.Stmt}
    (blockAt : f.blocks[bi]? = some block) (statement : block.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j)
    {env : Clif.Env} {program : Clif.Program} {MR : MemRelT} {isem : Backend.Proof.Sem}
    {before after : SourcePoint} (source : IndexedSourceInst env program f event.ctx bi record.inst before after)
    {frontier : ReadEffectFrontier event.ctx env program} {regs : Nat → CV} {world otherWorld : Arm.ArmState}
    {prefixRecords : List ScanRecord} {entry : Clif.Frame × Clif.Mem}
    (history : SourceReadCaptures event.ctx env program prefixRecords entry before.2 frontier.history)
    (retained : ∀ captured ∈ frontier.history,captured.record ∈ event.output.records)
    (pending : PendingReadMarks frontier record.output.state)
    (retiredMarks : RetiredReadUnmarked frontier record.output.state)
    (retiredValues : RetiredUndemanded frontier record.output.state)
    (related : PendingGuardedScanRel f result event.ctx bi env program MR frontier.history record.output.state before regs world)
    (otherRelated : PendingGuardedScanRel f result event.ctx bi env program MR frontier.history record.output.state before regs otherWorld) :
    ∃ next : ReadEffectFrontier event.ctx env program,
      seqRun (E2E.pairSem isem) (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs (world,otherWorld) = some (.fall regs (world,otherWorld)) ∧
      PendingGuardedScanRel f result event.ctx bi env program MR next.history record.input after regs world ∧
      PendingGuardedScanRel f result event.ctx bi env program MR next.history record.input after regs otherWorld ∧
      SourceReadCaptures event.ctx env program (prefixRecords++[record]) entry after.2 next.history ∧
      (∀ captured ∈ next.history,captured.record ∈ event.output.records) ∧
      PendingReadMarks next record.input ∧ RetiredReadUnmarked next record.input ∧ RetiredUndemanded next record.input := by
  obtain ⟨captured,recordEq,beforeEq,afterEq,executed,post⟩ := stock_lower_sunk_pending_transfer (isem := isem) run scope dominated
    events records marked blockAt statement current source related
  obtain ⟨other,otherRecord,otherBefore,otherAfter,_,otherPost⟩ := stock_lower_sunk_pending_transfer (isem := isem) run scope dominated
    events records marked blockAt statement current source otherRelated
  have same : other = captured := by
    cases captured
    cases other
    simp_all only [SunkReadSnapshot.mk.injEq]
  rw [same] at otherPost
  let next := frontier.capture captured
  have actual := ScansSpec.record_run (runScans_spec (stock_lower_event_scan_run run events)) record records
  have outputEq := Except.ok.inj (actual.symm.trans (scan_sunk event.ctx event.block record.inst event.termInst event.isBranch record.input marked))
  have stateEq : record.output.state = record.input := congrArg Scan.state outputEq
  have single := captured.source_capture
  rw [recordEq,beforeEq,afterEq] at single
  have combined := SourceReadCaptures.append history single
  refine ⟨next,?_,post,otherPost,combined,?_,?_,?_,?_⟩
  · have empty : record.output.emitted = #[] := congrArg Scan.emitted outputEq
    simp only [empty,Array.toList_empty,List.map_nil,seqRun]
  · intro actual member
    change actual ∈ frontier.history++[captured] at member
    rcases List.mem_append.mp member with earlier | current
    · exact retained actual earlier
    · have same := List.mem_singleton.mp current
      subst actual
      rwa [recordEq]
  · intro actual member
    change actual ∈ frontier.pending++[captured] at member
    rcases List.mem_append.mp member with earlier | current
    · rw [← stateEq]
      exact pending actual earlier
    · have same := List.mem_singleton.mp current
      subst actual
      rw [recordEq]
      exact marked
  · change RetiredReadUnmarked frontier record.input
    rw [← stateEq]
    exact retiredMarks
  · change RetiredUndemanded frontier record.input
    rw [← stateEq]
    exact retiredValues

end Backend.Stock.Proof.Acquire810
