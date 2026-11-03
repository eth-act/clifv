import FV.Backend.Proof.StockAcquireEncodedExtendPrefix

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E Isle Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Actual fallback records derive all width and fragment facts before concrete encoded transfer.
The final pipeline must supply its actual expanded/encoded lines and machine relation internally. -/
theorem stock_lower_fallback_extend_encoded {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (signed : Bool) {info : IInfo} {target : Clif.Ty} {x : Nat}
    (installed : event.ctx.insts[record.inst]? = some info)
    (source : info.clif = some (.extend (ScalarCast.extendOp signed) target x))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (ScalarCast.extendRule signed).id) :
    ∃ (sourceType : CTy) (pointer dest : Nat),event.ctx.valueType? x = some sourceType ∧
      event.ctx.valueReg? x = some (.vreg pointer .int) ∧ dest = record.input.base.nextVreg ∧
      record.output.emitted = #[.extend (.vreg dest .int) (.vreg pointer .int) signed sourceType.bits target.width] ∧
      ∀ (R : RL) (physical world : Arm.ArmState) (values : Loc → CV),StRel R physical values world →
        ∀ (env : Backend.Env) (machineDest machinePointer : Reg) (state next : PState) (lines : List Line),
          (MInst.extend machineDest machinePointer signed sourceType.bits target.width).lines R.ctx state = .ok (lines,next) →
          (∀ instruction trap,Line.ins instruction trap ∈ lines → ∃ arm,instruction.armFields env = .ok arm) →
          ∀ regs : Nat → CV,∃ nextRegs nextWorld,
            seqRun (csem R.F R.ctx R.X) (record.output.emitted.toList.map
              (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs world =
              some (.fall nextRegs nextWorld) ∧ SameWorld R.F nextWorld world ∧
            (∀ key,key ≠ aliasNum result.final.alias dest → nextRegs key = regs key) := by
  obtain ⟨sourceType,pointer,resultId,key,dest,typed,accepted,mapped,results,resultMap,fresh,output,chunk⟩ :=
    stock_lower_fallback_extend_record run scope dominated events records signed installed source recorded emitted selectedId
  have sourceWidth : sourceType.bits = 8 ∨ sourceType.bits = 16 ∨ sourceType.bits = 32 ∨ sourceType.bits = 64 := by
    simp only [eCTys,List.mem_cons,List.not_mem_nil,or_false] at accepted
    rcases accepted with rfl | rfl | rfl | rfl <;> decide
  have originalAccepted := ((stock_lower_record_context run scope events).1).instE record.inst info _ installed source
  have permitted : eTy target = true := by
    simpa [ScalarCast.extendOp,Compile.instE,Compile.tyE,eTy] using originalAccepted
  have targetWidth : target.width = 8 ∨ target.width = 16 ∨ target.width = 32 ∨ target.width = 64 := by
    cases target <;> simp [eTy,Clif.Ty.width] at permitted ⊢
  refine ⟨sourceType,pointer,dest,typed,mapped,fresh,chunk,?_⟩
  intro R physical world values related env machineDest machinePointer state next lines expanded encoded regs
  obtain ⟨nextRegs,nextWorld,executed,same,kept⟩ := regLevel_encoded_extend_prefix related sourceWidth targetWidth
    expanded encoded regs (dest := aliasNum result.final.alias dest) (pointer := aliasNum result.final.alias pointer)
  refine ⟨nextRegs,nextWorld,?_,same,kept⟩
  rw [chunk]
  change seqRun (csem R.F R.ctx R.X)
    [MInst.extend (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg dest .int))
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg pointer .int)) signed sourceType.bits target.width]
    regs world = _
  rw [resolve_vreg,resolve_vreg]
  exact executed

end Backend.Stock.Proof.Acquire810
