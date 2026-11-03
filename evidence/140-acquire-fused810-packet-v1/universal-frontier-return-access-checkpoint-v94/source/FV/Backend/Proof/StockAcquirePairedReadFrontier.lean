import FV.Backend.Proof.StockAcquireConsumerPairedFrontier
import FV.Backend.Proof.StockAcquireSunkPairedFrontier
import FV.Backend.Proof.StockAcquirePairedEntryFrontier

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- Internal execution state keeps the complete source history and every required binding in both worlds. -/
structure PairedReadFrontierAt (f : Clif.Function) (result : Result) (event : BlockScanEvent)
    (env : Clif.Env) (program : Clif.Program) (MR : MemRelT) (Z : BitVec 64 → Prop)
    (entry : Clif.Frame × Clif.Mem) (prefixRecords : List ScanRecord)
    (state : State) (point : SourcePoint) (regs : Nat → CV) (worlds : W2) where
  frontier : ReadEffectFrontier event.ctx env program
  history : SourceReadCaptures event.ctx env program prefixRecords entry point.2 frontier.history
  retained : ∀ captured ∈ frontier.history,captured.record ∈ event.output.records
  pending : PendingReadMarks frontier state
  retiredMarks : RetiredReadUnmarked frontier state
  retiredValues : RetiredUndemanded frontier state
  left : PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history state point regs worlds.1
  right : PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history state point regs worlds.2
  agreement : SameWorld Z worlds.1 worlds.2

/-- Actual sunk reads append one shared capture and preserve both machine states. -/
theorem stock_lower_sunk_paired_frontier_at {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (marked : record.input.sunk[record.inst]! = true)
    {j : Nat} {block : Clif.Block} {stm : Clif.Stmt}
    (blockAt : f.blocks[event.block]? = some block) (statement : block.body[j]? = some stm)
    (current : record.inst = blockStart f event.block+j)
    {env : Clif.Env} {program : Clif.Program} {MR : MemRelT} {Z : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    {before after : SourcePoint} (source : IndexedSourceInst env program f event.ctx event.block record.inst before after)
    {entry : Clif.Frame × Clif.Mem} {prefixRecords : List ScanRecord} {regs : Nat → CV} {worlds : W2}
    (prior : PairedReadFrontierAt f result event env program MR Z entry prefixRecords record.output.state before regs worlds) :
    ∃ post : PairedReadFrontierAt f result event env program MR Z entry (prefixRecords++[record]) record.input after regs worlds,
      seqRun (pairSem isem) (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs worlds = some (.fall regs worlds) := by
  obtain ⟨next,executed,left,right,history,retained,pending,retiredMarks,retiredValues⟩ :=
    stock_lower_sunk_paired_frontier_step (isem := isem) run scope dominated events records marked blockAt statement current source
      prior.history prior.retained prior.pending prior.retiredMarks prior.retiredValues prior.left prior.right
  exact ⟨⟨next,history,retained,pending,retiredMarks,retiredValues,left,right,prior.agreement⟩,executed⟩

/-- Actual selected consumers discharge their captured binding in both worlds and retire exactly that read. -/
theorem stock_lower_consumer_paired_frontier_at {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ R : SourceEndpointReceipt f event record,
      ∀ (env : Clif.Env) (program : Clif.Program) (entry before after : Clif.Frame × Clif.Mem),
      entry.1.body = R.block.body → SourceInstResult env program event.ctx record.inst before after →
      ∀ (F Z : BitVec 64 → Prop) (sb : Nat) (syms : String → Option Nat) (isem : Backend.Proof.Sem) (MR : MemRelT),
      (∀ a,F a → Z a) → MRStable F MR → MemRefines F sb syms isem → MemRelOk F sb syms f MR →
      ∀ (regs : Nat → CV) (worlds : W2),
      PairedReadFrontierAt f result event env program MR Z entry (event.output.records.reverse.take R.consumerIndex)
        record.output.state (R.consumerIndex,before) regs worlds →
      ∃ nextRegs nextWorlds, ∃ post : PairedReadFrontierAt f result event env program MR Z entry
          ((event.output.records.reverse.take R.consumerIndex)++[record]) record.input (R.consumerIndex+1,after) nextRegs nextWorlds,
        seqRun (pairSem isem) (record.output.emitted.toList.map
          (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs worlds = some (.fall nextRegs nextWorlds) := by
  obtain ⟨R,advance⟩ := stock_lower_acquire_consumer_paired_frontier_step run scope dominated events records recorded emitted selectedId
  refine ⟨R,?_⟩
  intro env program entry before after body source F Z sb syms isem MR frame stable memorySem memoryOk regs worlds prior
  obtain ⟨next,nextRegs,nextLeft,nextRight,executed,left,right,agreement,history,retained,pending,retiredMarks,retiredValues⟩ :=
    advance env program entry before after body source F Z sb syms isem MR frame stable memorySem memoryOk
      prior.frontier regs worlds.1 worlds.2 prior.history prior.pending prior.retiredMarks prior.retiredValues prior.left prior.right prior.agreement
  exact ⟨nextRegs,(nextLeft,nextRight),⟨next,history,retained,pending,retiredMarks,retiredValues,left,right,agreement⟩,executed⟩

end Backend.Stock.Proof.Acquire810
