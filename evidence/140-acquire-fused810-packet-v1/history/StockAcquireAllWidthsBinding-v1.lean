import FV.Backend.Proof.StockAcquireValueAllWidths
import FV.Backend.Proof.StockResults
import FV.Backend.Proof.StockEmittedScan

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Stock.runTerm emitInstruction

/-- Every admitted atomic width executes the actual fused instruction and holds the widened source value. -/
theorem acquire_pair_run {F : BitVec 64 → Prop} {sb : Nat}
    {syms : String → Option Nat} {isem : Backend.Proof.Sem} {MR : MemRelT}
    {f : Clif.Function} (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {cm cm' cm'' : Clif.Mem} {p z d nr : Nat}
    {pointer small widened : Clif.Val} {sourceTy targetTy : Clif.Ty}
    (atomicType : eTy sourceTy = true) (fits : targetTy.width ≤ 64)
    {flags : Clif.MemFlags} (little : flags.endianness ≠ some .big)
    (pointerSource : fr.regs p = some pointer) (pointerType : pointer.ty = .i64)
    {regs : Nat → CV} (pointerHeld : VHolds pointer (regs nr))
    (source : Clif.evalInst fr cm (.atomicLoad sourceTy flags p) = .ok ([small],cm'))
    (extension : Clif.evalInst (withValue fr z small) cm' (.extend .uextend targetTy z) =
      .ok ([widened],cm''))
    {world : Arm.ArmState} (memory : MR fr.slots cm world) :
    ∃ nextRegs nextWorld,cm' = cm ∧ cm'' = cm ∧
      seqRun isem [.loadAcquire (CTy.ofClif sourceTy) (.vreg d .int) (.vreg nr .int) flags]
        regs world = some (.fall nextRegs nextWorld) ∧
      VHolds widened (nextRegs d) ∧ (∀ key,key ≠ d → nextRegs key = regs key) ∧
      MR fr.slots cm nextWorld := by
  obtain ⟨raw,next,smallEq,sameMemory,sameFinal,held,executed,kept⟩ :=
    acquire_widened_value stable memorySem memoryOk atomicType fits little pointerSource pointerType
      pointerHeld source extension memory
  let operands : Array Operand := #[⟨nr,.int,.use,.early,.reg⟩,⟨d,.int,.def,.late,.reg⟩]
  let finalRegs := vdefUpd operands [ofX (raw.setWidth 64)] regs
  refine ⟨finalRegs,next,sameMemory,sameFinal,?_,?_,?_,kept⟩
  · exact seqRun_isem_one (operands_loadAcquire (CTy.ofClif sourceTy) d nr flags) executed rfl
  · simpa [finalRegs,operands,vdefUpd,writeV,Operand.isDef,Operand.isEarly,Operand.isLate,upd] using held
  · intro key different
    exact vdefUpd_other (by simpa [operands,Operand.isDef] using different)

/-- The real emitter binds its single virtual result without a copy or another memory instruction. -/
theorem acquire_emission_binding {ctx : Ctx} {ii : Nat} {info : IInfo} {z key d : Nat}
    (installed : ctx.insts[ii]? = some info) (results : info.results = [z])
    (mapped : ctx.valueReg? z = some (.vreg key .int))
    {before next : State} {trace : List RuleId}
    (root : Stock.runTerm ctx "lower" [.inst ii] before =
      .ok (some (.regsVec [[.vreg d .int]]),next,trace)) :
    ∃ emission,emitInstruction ctx ii before = .ok emission ∧
      emission.state = {next with alias := aliasStep next.alias (key,d)} ∧
      emission.code = next.base.emitted ∧ emission.results = [[.vreg d .int]] := by
  have binding := bindResults_virtual ctx next [(z,key,d)] (by
    intro pair member
    cases List.mem_singleton.mp member
    exact mapped)
  let emission : Emission := ⟨{next with alias := aliasStep next.alias (key,d)},
    next.base.emitted,[[.vreg d .int]],trace⟩
  have infoBang : ctx.insts[ii]! = info := by simp only [getElem!_def,installed]
  refine ⟨emission,?_,rfl,rfl,rfl⟩
  unfold emitInstruction
  rw [infoBang,root]
  simp [results,binding,emission]

/-- Actual emitted scan records retain the same virtual binding and exact output tuple. -/
theorem acquire_record_binding {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {z key d : Nat}
    (installed : event.ctx.insts[record.inst]? = some info) (results : info.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg key .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {next : State} {trace : List RuleId}
    (root : Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
      .ok (some (.regsVec [[.vreg d .int]]),next,trace)) :
    (record.output.state.alias[key]?).join = some d ∧ step.results = [[.vreg d .int]] ∧
      record.output.emitted = next.base.emitted := by
  obtain ⟨emission,emissionRun,state,code,output⟩ := acquire_emission_binding installed results mapped root
  obtain ⟨actual,actualRun,actualScan⟩ := stock_emitted_scan (record_execute run events records) recorded emitted
  have same : actual = emission := Except.ok.inj (actualRun.symm.trans emissionRun)
  subst actual
  rw [actualScan] at recorded
  have stepEq := Option.some.inj recorded.symm
  refine ⟨?_,?_,?_⟩
  · rw [actualScan]
    change (emission.state.alias[key]?).join = some d
    rw [state]
    exact (aliasStep_get next.alias (key,d) key).trans (by simp)
  · rw [stepEq]
    exact output
  · rw [actualScan]
    exact code

end Backend.Stock.Proof.Acquire810
