import FV.Backend.Proof.StockAcquireOmittedPendingRefines
import FV.Backend.Proof.StockAcquirePairedReadFrontier

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- Actual omitted records have no sunk mark of their own. -/
theorem stock_lower_omitted_record_unsunk {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (omitted : step.decision = .omitted) :
    record.input.sunk[record.inst]! = false := by
  have actual := stock_fence_record_execute run events records
  cases marked : record.input.sunk[record.inst]! with
  | false => rfl
  | true =>
    have outputEq := Except.ok.inj (actual.symm.trans
      (scan_sunk event.ctx event.block record.inst event.termInst event.isBranch record.input marked))
    rw [outputEq] at recorded
    have equal := Option.some.inj recorded.symm
    have wrong := congrArg Step.decision equal
    rw [omitted] at wrong
    cases wrong

/-- Omitted ordinary source records preserve the complete paired pending frontier.
Actual scan execution supplies empty code and mark persistence. -/
theorem stock_lower_omitted_paired_frontier_at {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[event.block]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block + j)
    {step : Step} (recorded : record.output.step = some step) (omitted : step.decision = .omitted)
    {isem : Backend.Proof.Sem} {MR : MemRelT} {Z : BitVec 64 → Prop}
    {env : Clif.Env} {cp : Clif.Program}
    {entry : Clif.Frame × Clif.Mem} {prefixRecords : List ScanRecord} {before after : SourcePoint}
    (sourceStep : IndexedSourceInst env cp f event.ctx event.block record.inst before after)
    {regs : Nat → CV} {worlds : W2}
    (prior : PairedReadFrontierAt f result event env cp MR Z entry prefixRecords
      record.output.state before regs worlds) :
    ∃ post : PairedReadFrontierAt f result event env cp MR Z entry (prefixRecords++[record])
        record.input after regs worlds,
      post.frontier = prior.frontier ∧
      seqRun (pairSem isem) (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        regs worlds = some (.fall regs worlds) := by
  have actual := stock_fence_record_execute run events records
  have facts := scan_omitted actual recorded omitted
  have code := facts.2.2.2.2.2.2.2.1
  have stateEq := facts.2.2.2.2.2.2.2.2
  have sunkEq : record.output.state.sunk = record.input.sunk := by rw [stateEq,scanState_sunk]
  have demandEq : record.output.state.demand = record.input.demand := by rw [stateEq,scanState_demands]
  have single := stock_lower_omitted_pending_refines (isem := isem) (MR := MR) run scope dominated events records
    block statement current recorded omitted prior.frontier.history
  obtain ⟨leftRegs,leftWorld,leftRun,leftPost⟩ := single before after sourceStep regs worlds.1 prior.left
  obtain ⟨rightRegs,rightWorld,rightRun,rightPost⟩ := single before after sourceStep regs worlds.2 prior.right
  simp only [code,Array.toList_empty,List.map_nil,seqRun] at leftRun rightRun
  have leftEq := SeqEnd.fall.inj (Option.some.inj leftRun).symm
  have rightEq := SeqEnd.fall.inj (Option.some.inj rightRun).symm
  rw [leftEq.1,leftEq.2] at leftPost
  rw [rightEq.1,rightEq.2] at rightPost
  have unmarked := stock_lower_omitted_record_unsunk run events records recorded omitted
  have one : SourceReadCaptures event.ctx env cp [record] before.2 after.2 [] :=
    .skipped unmarked sourceStep.2.2 (.nil after.2)
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
  have retiredValues := retired_undemanded_of_le (after := record.input) prior.retiredValues
    (fun value => by rw [demandEq];exact Nat.le_refl _)
  refine ⟨⟨prior.frontier,history,prior.retained,pending,retiredMarks,retiredValues,
    leftPost,rightPost,prior.agreement⟩,rfl,?_⟩
  simp only [code,Array.toList_empty,List.map_nil,seqRun]

end Backend.Stock.Proof.Acquire810
