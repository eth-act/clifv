import FV.Backend.Proof.StockMemoryReadTransport
import FV.Backend.Proof.StockMemoryExtLoadSelected
import FV.Backend.Proof.StockMemoryExtLoadRecordValues

namespace Backend.Stock.Memory.ExtendedRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The actual retained and finally resolved load record executes on two
source-related worlds with one exact resulting virtual file. Original source
metadata derives selection, code, result binding and aliases internally. The
existing guarded memory semantics is supported through initialized source reads. -/
theorem stock_lower_extending_load_paired_record (kind : Kind) {ty : Clif.Ty}
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {z a x nreg : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.load kind.sourceOp ty flags x 0)) (results : info.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    (parameter : event.ctx.defInst? x = none) (pointer : event.ctx.valueReg? x = some (.vreg nreg .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F Rd : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Sem} {MR : MemRelT}
    (memorySem : MemRefinesR Rd F sb syms isem) (memoryOk : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {cm cm' : Clif.Mem} {w w' : Arm.ArmState} {ρ : Nat → CV} {vals : List Clif.Val}
    (memory : MR fr.slots cm w) (other : MR fr.slots cm w') (reads : InitIn Rd cm)
    (dfg : DFGCons event.ctx fr)
    (operands : ValueHeld event.ctx fr (fun k => ρ (aliasNum result.final.alias k)) x)
    (evaluated : Clif.evalInst fr cm (.load kind.sourceOp ty flags x 0) = .ok (vals,cm')) :
    ∃ ρ' t t',seqRun isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w = some (.fall ρ' t) ∧
      seqRun isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w' = some (.fall ρ' t') ∧
      SameWorld F t w ∧ SameWorld F t' w' := by
  obtain ⟨little,out,next,trace,rhsTrace,rootRun,evalRun⟩ := stock_lower_extending_load_selected_receipts kind
    run scope events records source clif recorded emitted
  obtain ⟨outputs,code,upper,finalAlias,demand⟩ := stock_lower_extending_load_record_full kind run scope dominated events records
    source clif results mapped parameter pointer recorded emitted (n := 999879) evalRun rootRun
  have frontier : (scanState record.input record.inst).base.nextVreg = record.input.base.nextVreg := by
    unfold scanState; dsimp only; split <;> rfl
  have bound : result.final.alias.size ≤ record.input.base.nextVreg := by
    simpa only [frontier] using stock_lower_blockScanAliasBounds run event events record records
  have fixed : aliasNum result.final.alias record.input.base.nextVreg = record.input.base.nextVreg := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bound]
    rfl
  have resolved : record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) =
      [.load kind.loadOp (.vreg record.input.base.nextVreg .int)
        (.unsignedOffset (.vreg (aliasNum result.final.alias nreg) .int) 0) flags] := by
    rw [code]
    change [MInst.load kind.loadOp
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg record.input.base.nextVreg .int))
      (.unsignedOffset (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg nreg .int)) 0) flags] = _
    rw [resolve_vreg,resolve_vreg]
    change [MInst.load kind.loadOp (.vreg (aliasNum result.final.alias record.input.base.nextVreg) .int)
      (.unsignedOffset (.vreg (aliasNum result.final.alias nreg) .int) 0) flags] = _
    rw [fixed]
  have pointerTy := (stock_lower_record_context run scope events).1.addr64 _ _ _ x source clif rfl
  have address := fun world => mapped_unsigned_address (sb := sb) (bytes := kind.loadOp.bytes) (w := world)
    operands pointer dfg pointerTy (off := 0) (by cases kind <;> decide)
  obtain ⟨value,t,t',executed,otherRun,same,otherSame⟩ := load_source_result_pairR memorySem memoryOk
    memory other reads (aop := kind.loadOp) (d := record.input.base.nextVreg)
    (am := .unsignedOffset (.vreg (aliasNum result.final.alias nreg) .int) 0)
    (uses := [ρ (aliasNum result.final.alias nreg)]) (by cases kind <;> decide)
    (by cases kind <;> rfl) little
    (fun pv hpv => by simpa [amodeAddr,LoadOp.bytes] using address w pv hpv)
    (fun pv hpv => by simpa [amodeAddr,LoadOp.bytes] using address w' pv hpv) evaluated
  have operands := load_ops kind.loadOp record.input.base.nextVreg
    (am := .unsignedOffset (.vreg (aliasNum result.final.alias nreg) .int) 0)
    (by intro r member; exact ⟨_,List.mem_singleton.mp member⟩) flags
  obtain ⟨ops,opsEq,uses,defs,update⟩ := operands.ops
  have usesEq : vuses ops ρ = [ρ (aliasNum result.final.alias nreg)] := uses ρ
  rw [← usesEq] at executed otherRun
  have first := seqRun_isem_one opsEq executed (by rw [defs]; rfl)
  have second := seqRun_isem_one opsEq otherRun (by rw [defs]; rfl)
  rw [update] at first second
  refine ⟨upd ρ record.input.base.nextVreg value,t,t',?_,?_,same,otherSame⟩
  · rwa [resolved]
  · rwa [resolved]

end Backend.Stock.Memory.ExtendedRoots
