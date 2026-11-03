import FV.Backend.Proof.StockAcquireReadBeforeLaterFault

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A real sunk record advances the compiler boundary without evaluating the fixed faulting source point. -/
theorem stock_lower_sunk_frozen_frontier_step {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (marked : record.input.sunk[record.inst]! = true)
    {env : Clif.Env} {program : Clif.Program} {MR : MemRelT} {isem : Backend.Proof.Sem}
    {frontier : ReadEffectFrontier event.ctx env program} {point : SourcePoint}
    {regs : Nat → CV} {world : Arm.ArmState}
    (related : PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history record.output.state point regs world)
    (pending : PendingReadMarks frontier record.output.state)
    (retiredMarks : RetiredReadUnmarked frontier record.output.state)
    (retiredValues : RetiredUndemanded frontier record.output.state) :
    record.output.state = record.input ∧
    seqRun isem (record.output.emitted.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs world =
        some (.fall regs world) ∧
    PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history record.input point regs world ∧
    PendingReadMarks frontier record.input ∧ RetiredReadUnmarked frontier record.input ∧ RetiredUndemanded frontier record.input := by
  have actual := ScansSpec.record_run (runScans_spec (stock_lower_event_scan_run run events)) record records
  have equal := Except.ok.inj (actual.symm.trans
    (scan_sunk event.ctx event.block record.inst event.termInst event.isBranch record.input marked))
  have stateEq : record.output.state = record.input := congrArg Scan.state equal
  have codeEq : record.output.emitted = #[] := congrArg Scan.emitted equal
  refine ⟨stateEq,?_,?_,?_,?_,?_⟩
  · rw [codeEq]
    rfl
  · rwa [← stateEq]
  · rwa [← stateEq]
  · rwa [← stateEq]
  · rwa [← stateEq]

end Backend.Stock.Proof.Acquire810
