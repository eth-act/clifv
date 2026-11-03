import FV.Backend.Proof.StockAcquireFencePendingRefines
import FV.Backend.Proof.StockAcquireReadBeforeLaterFault

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Actual fence code advances the compiler frontier at the fixed source fault point.
The proof does not evaluate a later source instruction or change the pending queue. -/
theorem stock_lower_fence_frozen_frontier_step {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some .fence)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {program : Clif.Program}
    {frontier : ReadEffectFrontier event.ctx env program} {point : SourcePoint}
    {regs : Nat → CV} {world : Arm.ArmState}
    (related : PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history
      record.output.state point regs world)
    (pending : PendingReadMarks frontier record.output.state)
    (retiredMarks : RetiredReadUnmarked frontier record.output.state)
    (retiredValues : RetiredUndemanded frontier record.output.state) :
    ∃ nextWorld,
      seqRun isem (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        regs world = some (.fall regs nextWorld) ∧ SameWorld F nextWorld world ∧
      PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history record.input point regs nextWorld ∧
      PendingReadMarks frontier record.input ∧ RetiredReadUnmarked frontier record.input ∧
      RetiredUndemanded frontier record.input := by
  obtain ⟨step,recorded,emitted,results,selected,code,frame⟩ := stock_lower_fence_record_exact
    run scope events records source clif
  have demandEq : record.output.state.demand = record.input.demand := by
    rw [frame]
    exact scanState_demands _ _
  have sunkEq : record.output.state.sunk = record.input.sunk := by
    rw [frame]
    exact scanState_sunk _ _
  obtain ⟨nextWorld,executed,same⟩ := stock_lower_fence_execute run scope events records source clif
    refines result.final.alias regs world
  refine ⟨nextWorld,executed,same,?_,?_,?_,?_⟩
  · refine ⟨related.1,related.2.1,stable _ _ _ _ same.toNF related.2.2.1,?_⟩
    simpa only [PendingValuesHeld,Demanded,demandEq] using related.2.2.2
  · intro captured member
    rw [← sunkEq]
    exact pending captured member
  · intro captured member
    rw [← sunkEq]
    exact retiredMarks captured member
  · simpa only [RetiredUndemanded,demandEq] using retiredValues

end Backend.Stock.Proof.Acquire810
