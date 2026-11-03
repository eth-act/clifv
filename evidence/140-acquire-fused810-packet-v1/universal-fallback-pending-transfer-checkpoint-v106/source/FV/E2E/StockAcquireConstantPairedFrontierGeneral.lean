import FV.E2E.StockAcquireConstantPairedFreshRun
import FV.Backend.Proof.StockAcquireConstantPendingRefines
import FV.Backend.Proof.StockAcquireEmptyMarksPairedFrontier
import FV.Backend.Proof.StockAcquireReadPrefixPaired

namespace E2E.StockAcquirePending
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- Actual constant records advance the full paired frontier with an arbitrary disagreement set.
The original driver contract supplies alias semantics. No TLS or caller execution certificate is required. -/
theorem stock_lower_constant_paired_frontier_general {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[event.block]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block + j)
    {info : IInfo} {ty : Clif.Ty} {imm : BitVec ty.width} {x a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.iconst ty imm))
    (results : info.results = [x]) (statementResults : stm.results = [x])
    (mapped : event.ctx.valueReg? x = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F Z : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (driver : DriverSem isem) (includes : ∀ addr,F addr → Z addr)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program}
    {entry : Clif.Frame × Clif.Mem} {prefixRecords : List ScanRecord} {before after : SourcePoint}
    (sourceStep : IndexedSourceInst env cp f event.ctx event.block record.inst before after)
    {regs : Nat → CV} {worlds : W2}
    (prior : PairedReadFrontierAt f result event env cp MR Z entry prefixRecords
      record.output.state before regs worlds) :
    ∃ nextRegs nextWorlds,∃ post : PairedReadFrontierAt f result event env cp MR Z entry
        (prefixRecords++[record]) record.input after nextRegs nextWorlds,
      post.frontier = prior.frontier ∧
      seqRun (pairSem isem) (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        regs worlds = some (.fall nextRegs nextWorlds) := by
  have single := stock_lower_constant_pending_refines run scope dominated events records block statement current
    source clif results statementResults mapped recorded emitted refines driver stable prior.frontier.history
  obtain ⟨leftRegs,leftWorld,leftRun,leftPost⟩ := single before after sourceStep regs worlds.1 prior.left
  obtain ⟨rightRegs,rightWorld,rightRun,rightPost⟩ := single before after sourceStep regs worlds.2 prior.right
  obtain ⟨definitions,nextRegs,nextWorlds,executed,leftFrame,rightFrame,agreement⟩ :=
    stock_lower_constant_paired_fresh_run run scope events records source clif results mapped recorded emitted
      refines includes regs worlds prior.agreement
  obtain ⟨leftActual,rightActual⟩ := StockAcquirePair.seqRun_paired_fall_projections executed
  have leftEq := SeqEnd.fall.inj (Option.some.inj (leftRun.symm.trans leftActual))
  have rightEq := SeqEnd.fall.inj (Option.some.inj (rightRun.symm.trans rightActual))
  rw [leftEq.1,leftEq.2] at leftPost
  rw [rightEq.1,rightEq.2] at rightPost
  have marks := stock_lower_constant_empty_marks run scope events records source clif results mapped
    recorded emitted refines
  obtain ⟨post,same,runCode⟩ := stock_lower_empty_marks_paired_frontier_at run events records recorded emitted
    marks sourceStep prior executed leftPost rightPost agreement
  exact ⟨nextRegs,nextWorlds,post,same,runCode⟩

end E2E.StockAcquirePending
