import FV.Backend.Proof.StockAcquireFencePendingRefines
import FV.Backend.Proof.StockAcquireEmptyMarksPairedFrontier

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- Actual fence emission discharges the empty-group branch with the complete pending queue.
Both worlds retain every required binding. The source fence preserves memory and cannot replace a read fault. -/
theorem stock_lower_fence_paired_frontier_at {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} (found : event.ctx.insts[record.inst]? = some info) (original : info.clif = some .fence)
    {F Z : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (worldFrame : ∀ a,F a → Z a)
    {env : Clif.Env} {program : Clif.Program} {MR : MemRelT} (stable : MRStable F MR)
    {entry : Clif.Frame × Clif.Mem} {prefixRecords : List ScanRecord} {before after : SourcePoint}
    (source : IndexedSourceInst env program f event.ctx event.block record.inst before after)
    {regs : Nat → CV} {worlds : W2}
    (prior : PairedReadFrontierAt f result event env program MR Z entry prefixRecords record.output.state before regs worlds) :
    ∃ nextWorlds,∃ post : PairedReadFrontierAt f result event env program MR Z entry
        (prefixRecords++[record]) record.input after regs nextWorlds,
      post.frontier = prior.frontier ∧
      seqRun (pairSem isem) (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs worlds = some (.fall regs nextWorlds) := by
  obtain ⟨step,recorded,emitted,results,selected,code,frame⟩ := stock_lower_fence_record_exact run scope events records found original
  have actualCode : record.output.emitted.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) = [.fence] := by
    rw [code];rfl
  have single := stock_lower_fence_pending_refines run scope dominated events records found original refines
    env program MR stable prior.frontier.history
  obtain ⟨leftRegs,left,runLeft,postLeft⟩ := single before after source regs worlds.1 prior.left
  obtain ⟨rightRegs,right,runRight,postRight⟩ := single before after source regs worlds.2 prior.right
  obtain ⟨expectedLeft,first,sameLeft⟩ := refines .fence [] worlds.1 [] worlds.1 (ctl := .next) rfl
  obtain ⟨expectedRight,second,sameRight⟩ := refines .fence [] worlds.2 [] worlds.2 (ctl := .next) rfl
  have firstRun := seqRun_isem_one (i := .fence) (ops := #[]) (ρ := regs) rfl first rfl
  have secondRun := seqRun_isem_one (i := .fence) (ops := #[]) (ρ := regs) rfl second rfl
  change seqRun isem [.fence] regs worlds.1 = some (.fall regs expectedLeft) at firstRun
  change seqRun isem [.fence] regs worlds.2 = some (.fall regs expectedRight) at secondRun
  rw [actualCode] at runLeft runRight
  have leftEq := SeqEnd.fall.inj (Option.some.inj (runLeft.symm.trans firstRun))
  have rightEq := SeqEnd.fall.inj (Option.some.inj (runRight.symm.trans secondRun))
  rw [leftEq.1,leftEq.2] at postLeft
  rw [rightEq.1,rightEq.2] at postRight
  have paired := pairSem_eq (p := worlds) first second
  have execution : seqRun (pairSem isem) [.fence] regs worlds = some (.fall regs (expectedLeft,expectedRight)) := by
    have operands : MInst.fence.operands = .ok #[] := rfl
    have actual : pairSem isem .fence (vuses #[] regs) worlds = some ([],(expectedLeft,expectedRight),.next) := paired
    simp only [seqRun,operands,actual]
    rfl
  have marks : PendingMarks event.ctx (scanState record.input record.inst) [] record.output.state := by
    apply PendingMarks.frame (middle := record.output.state)
    · rw [frame]
    · rw [frame]
    · rw [frame]
    · exact .nil _
  have agreement := SameWorld.trans (SameWorld.mono worldFrame sameLeft)
    (SameWorld.trans prior.agreement (SameWorld.symm (SameWorld.mono worldFrame sameRight)))
  obtain ⟨post,unchanged,executed⟩ := stock_lower_empty_marks_paired_frontier_at run events records recorded emitted marks source prior
    (by rw [actualCode];exact execution) postLeft postRight agreement
  exact ⟨(expectedLeft,expectedRight),post,unchanged,executed⟩

end Backend.Stock.Proof.Acquire810
