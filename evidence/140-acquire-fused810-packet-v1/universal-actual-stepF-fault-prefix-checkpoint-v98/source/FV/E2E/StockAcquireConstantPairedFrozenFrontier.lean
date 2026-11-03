import FV.E2E.StockAcquireConstantPairedFreshRun
import FV.Backend.Proof.StockAcquireConstantFrozenFrontier
import FV.Backend.Proof.StockAcquireReadPrefixPaired

namespace E2E.StockAcquirePending
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
open Backend.Stock.Proof
open Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Actual constant execution preserves both pending relations at the same fixed source fault point.
The whole capture history remains fixed. No later source instruction executes. -/
theorem stock_lower_constant_paired_frozen_frontier {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {ty : Clif.Ty} {imm : BitVec ty.width} {x a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.iconst ty imm))
    (results : info.results = [x]) (mapped : event.ctx.valueReg? x = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {bi j : Nat} {block : Clif.Block} {statement : Clif.Stmt}
    (blockAt : f.blocks[bi]? = some block) (statementAt : block.body[j]? = some statement)
    (current : record.inst = blockStart f bi+j)
    {F Z : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (includes : ∀ addr,F addr → Z addr)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {program : Clif.Program}
    {frontier : ReadEffectFrontier event.ctx env program} {point : SourcePoint}
    (order : point.1 ≤ j) {regs : Nat → CV} {worlds : W2}
    (left : PendingGuardedScanRel f result event.ctx bi env program MR frontier.history
      record.output.state point regs worlds.1)
    (right : PendingGuardedScanRel f result event.ctx bi env program MR frontier.history
      record.output.state point regs worlds.2)
    (agreement : SameWorld Z worlds.1 worlds.2)
    (pending : PendingReadMarks frontier record.output.state)
    (retiredMarks : RetiredReadUnmarked frontier record.output.state)
    (retiredValues : RetiredUndemanded frontier record.output.state) :
    ∃ nextRegs after,
      seqRun (pairSem isem) (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        regs worlds = some (.fall nextRegs after) ∧
      PendingGuardedScanRel f result event.ctx bi env program MR frontier.history record.input point nextRegs after.1 ∧
      PendingGuardedScanRel f result event.ctx bi env program MR frontier.history record.input point nextRegs after.2 ∧
      SameWorld Z after.1 after.2 ∧ PendingReadMarks frontier record.input ∧
      RetiredReadUnmarked frontier record.input ∧ RetiredUndemanded frontier record.input := by
  obtain ⟨definitions,nextRegs,after,executed,leftFrame,rightFrame,related⟩ :=
    stock_lower_constant_paired_fresh_run run scope events records source clif results mapped recorded emitted
      refines includes regs worlds agreement
  obtain ⟨leftRun,rightRun⟩ := StockAcquirePair.seqRun_paired_fall_projections executed
  have postLeft := stock_lower_pending_frozen_source_frame run scope dominated events records blockAt statementAt
    current recorded emitted stable order left definitions leftRun leftFrame
  have postRight := stock_lower_pending_frozen_source_frame run scope dominated events records blockAt statementAt
    current recorded emitted stable order right definitions rightRun rightFrame
  have marks := stock_lower_constant_empty_marks run scope events records source clif results mapped
    recorded emitted refines
  have sunkEq : record.output.state.sunk = record.input.sunk := by
    simpa only [List.foldl_nil,scanState_sunk] using marks.sunk_exact
  refine ⟨nextRegs,after,executed,postLeft,postRight,related,?_,?_,?_⟩
  · intro captured member
    rw [← sunkEq]
    exact pending captured member
  · intro captured member
    rw [← sunkEq]
    exact retiredMarks captured member
  · exact retired_undemanded_of_le retiredValues
      (stock_lower_record_demand_mono run events records recorded emitted)

end E2E.StockAcquirePending
