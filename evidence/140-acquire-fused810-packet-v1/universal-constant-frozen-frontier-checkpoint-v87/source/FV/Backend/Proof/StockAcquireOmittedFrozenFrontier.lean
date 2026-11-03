import FV.Backend.Proof.StockAcquireOmittedPendingRefines
import FV.Backend.Proof.StockAcquireReadBeforeLaterFault

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual omission advances the compiler boundary at a fixed source fault point.
No later source instruction executes. Inherited marks and all required bindings remain. -/
theorem stock_lower_omitted_frozen_frontier_step {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (omitted : step.decision = .omitted)
    {env : Clif.Env} {program : Clif.Program} {MR : MemRelT} {isem : Backend.Proof.Sem}
    {frontier : ReadEffectFrontier event.ctx env program} {point : SourcePoint}
    {regs : Nat → CV} {world : Arm.ArmState}
    (related : PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history
      record.output.state point regs world)
    (pending : PendingReadMarks frontier record.output.state)
    (retiredMarks : RetiredReadUnmarked frontier record.output.state)
    (retiredValues : RetiredUndemanded frontier record.output.state) :
    seqRun isem (record.output.emitted.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
      regs world = some (.fall regs world) ∧
    PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history record.input point regs world ∧
    PendingReadMarks frontier record.input ∧ RetiredReadUnmarked frontier record.input ∧
    RetiredUndemanded frontier record.input := by
  have actual := stock_fence_record_execute run events records
  have facts := scan_omitted actual recorded omitted
  have code := facts.2.2.2.2.2.2.2.1
  have stateEq := facts.2.2.2.2.2.2.2.2
  have sunkEq : record.output.state.sunk = record.input.sunk := by rw [stateEq,scanState_sunk]
  have demandEq : record.output.state.demand = record.input.demand := by rw [stateEq,scanState_demands]
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [code]
    rfl
  · refine ⟨related.1,related.2.1,related.2.2.1,?_⟩
    simpa only [PendingValuesHeld,Demanded,demandEq] using related.2.2.2
  · intro captured member
    rw [← sunkEq]
    exact pending captured member
  · intro captured member
    rw [← sunkEq]
    exact retiredMarks captured member
  · simpa only [RetiredUndemanded,demandEq] using retiredValues

end Backend.Stock.Proof.Acquire810
