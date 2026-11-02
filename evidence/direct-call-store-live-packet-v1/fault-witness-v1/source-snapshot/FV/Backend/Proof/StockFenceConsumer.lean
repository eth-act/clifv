import FV.Backend.Proof.StockFenceBarrier
import FV.Backend.Proof.StockFenceTrapOrder

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

/-- A fence contract for checker, compiler and generated-proof consumers.
The contract records actual driver results and adds no source classifier. -/
structure FenceRecordContract (event : BlockScanEvent) (record : ScanRecord) : Prop where
  selected : ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧
    step.results = [] ∧ step.rules.getLast? = some 1024
  code : record.output.emitted = #[.fence]
  state : record.output.state = {scanState record.input record.inst with
    base := (scanState record.input record.inst).base.emit .fence}
  positive : record.input.entryColor[record.inst]! ≠ 0
  color : record.output.state.color = some record.input.entryColor[record.inst]!
  replay : checkScan event.ctx event.block record.inst event.termInst event.isBranch
    record.input record.output = true
  fall : ∀ {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem},Refines F isem →
    ∀ (aliases : Array (Option Nat)) (env : Clif.Env) (cp : Clif.Program)
      (MR : Clif.Mem → Arm.ArmState → Prop),
      (∀ cm w w',SameWorldNF F w' w → MR cm w → MR cm w') →
      ScanFallRefines (SourceInstResult env cp event.ctx) isem aliases
        (fun st s ρ w => MR s.2 w ∧ ValuesHeld (Demanded st) event.ctx s.1
          (fun k => ρ (aliasNum aliases k))) record
  firstTrap : ∀ {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem},Refines F isem →
    ∀ (aliases : Array (Option Nat)) (ρ : Nat → CV) (w : Arm.ArmState),
      ∃ world,SameWorld F world w ∧ ∀ (rest : List MInst) (code : Clif.TrapCode),
        TrapRun isem rest ρ world code →
          TrapRun isem ((record.output.emitted.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ++ rest) ρ w code

/-- The real driver discharges every fence contract field under original scope. -/
theorem stock_lower_fence_contract {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} (found : event.ctx.insts[record.inst]? = some info)
    (source : info.clif = some .fence) : FenceRecordContract event record := by
  obtain ⟨step,recorded,emitted,resultRegs,last,code,frame⟩ :=
    stock_lower_fence_record_exact run scope events records found source
  have barrier := stock_lower_fence_barrier run scope events records found source
  exact ⟨⟨step,recorded,emitted,resultRegs,last⟩,code,frame,barrier.1,barrier.2,
    checkScan_complete (stock_fence_record_execute run events records),
    fun hR aliases env cp MR stable => stock_lower_fence_fall_refines run scope events records
      found source hR aliases env cp MR stable,
    fun hR aliases ρ w => stock_lower_fence_first_trap run scope events records
      found source hR aliases ρ w⟩

end Backend.Stock.Proof
