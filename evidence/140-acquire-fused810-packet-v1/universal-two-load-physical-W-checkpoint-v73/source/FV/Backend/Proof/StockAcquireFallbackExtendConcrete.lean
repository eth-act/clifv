import FV.Backend.Proof.StockAcquireFallbackExtendRecord

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E Isle Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Actual fallback lowering and final aliases derive the concrete small-extension transfer.
The small-width branch is internal case analysis; other source widths remain separate proof obligations. -/
theorem stock_lower_fallback_unsigned_small_concrete {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {target : Clif.Ty} {x : Nat}
    (installed : event.ctx.insts[record.inst]? = some info)
    (source : info.clif = some (.extend .uextend target x))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 808) :
    ∃ (sourceType : CTy) (pointer dest : Nat),
      event.ctx.valueType? x = some sourceType ∧ sourceType ∈ eCTys ∧
      event.ctx.valueReg? x = some (.vreg pointer .int) ∧ dest = record.input.base.nextVreg ∧
      record.output.emitted = #[.extend (.vreg dest .int) (.vreg pointer .int) false sourceType.bits target.width] ∧
      ∀ (R : RL) (physical world : Arm.ArmState) (values : Loc → CV),StRel R physical values world →
        sourceType.bits = 8 ∨ sourceType.bits = 16 → ∀ regs : Nat → CV,
        ∃ nextRegs nextWorld,
          seqRun (csem R.F R.ctx R.X) (record.output.emitted.toList.map
            (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs world =
            some (.fall nextRegs nextWorld) ∧ SameWorld R.F nextWorld world ∧
          (∀ key,key ≠ aliasNum result.final.alias dest → nextRegs key = regs key) := by
  obtain ⟨sourceType,pointer,resultId,key,dest,typed,accepted,mapped,results,resultMap,fresh,output,chunk⟩ :=
    stock_lower_fallback_extend_record run scope dominated events records false installed source recorded emitted selectedId
  refine ⟨sourceType,pointer,dest,typed,accepted,mapped,fresh,chunk,?_⟩
  intro R physical world values related width regs
  obtain ⟨nextRegs,nextWorld,executed,same,kept⟩ := regLevel_unsigned_small_extend_prefix related width regs
    (dest := aliasNum result.final.alias dest) (pointer := aliasNum result.final.alias pointer) (toB := target.width)
  refine ⟨nextRegs,nextWorld,?_,same,kept⟩
  rw [chunk]
  change seqRun (csem R.F R.ctx R.X)
    [MInst.extend (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg dest .int))
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg pointer .int)) false sourceType.bits target.width]
    regs world = _
  rw [resolve_vreg,resolve_vreg]
  exact executed

end Backend.Stock.Proof.Acquire810
