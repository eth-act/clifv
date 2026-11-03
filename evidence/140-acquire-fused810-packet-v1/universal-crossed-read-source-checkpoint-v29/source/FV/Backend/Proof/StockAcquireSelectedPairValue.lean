import FV.Backend.Proof.StockAcquireSelectedTargetWidth

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Actual record selection discharges the target-width condition of acquire value execution.
Source and memory relations retain their original conditions. -/
theorem acquire_selected_pair_run {F : BitVec 64 → Prop} {sb : Nat}
    {syms : String → Option Nat} {isem : Backend.Proof.Sem} {MR : MemRelT}
    {f : Clif.Function} (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {cm cm' cm'' : Clif.Mem} {p z d nr : Nat}
    {pointer small widened : Clif.Val} {sourceTy targetTy : Clif.Ty}
    (atomicType : eTy sourceTy = true)
    {flags : Clif.MemFlags} (little : flags.endianness ≠ some .big)
    (pointerSource : fr.regs p = some pointer) (pointerType : pointer.ty = .i64)
    {regs : Nat → CV} (pointerHeld : VHolds pointer (regs nr))
    (source : Clif.evalInst fr cm (.atomicLoad sourceTy flags p) = .ok ([small],cm'))
    (extension : Clif.evalInst (withValue fr z small) cm' (.extend .uextend targetTy z) =
      .ok ([widened],cm''))
    {result : Result} (lowerRun : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} (installed : event.ctx.insts[record.inst]? = some info)
    (selectedSource : info.clif = some (.extend .uextend targetTy z))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810)
    {world : Arm.ArmState} (memory : MR fr.slots cm world) :
    ∃ nextRegs nextWorld,cm' = cm ∧ cm'' = cm ∧
      seqRun isem [.loadAcquire (CTy.ofClif sourceTy) (.vreg d .int) (.vreg nr .int) flags]
        regs world = some (.fall nextRegs nextWorld) ∧
      VHolds widened (nextRegs d) ∧ (∀ key,key ≠ d → nextRegs key = regs key) ∧
      MR fr.slots cm nextWorld := by
  have fits := stock_lower_acquire_selected_target_width lowerRun scope events records installed
    selectedSource recorded emitted selectedId
  exact acquire_pair_run stable memorySem memoryOk atomicType fits little pointerSource pointerType
    pointerHeld source extension memory

end Backend.Stock.Proof.Acquire810
