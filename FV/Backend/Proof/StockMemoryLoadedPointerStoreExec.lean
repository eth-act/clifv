import FV.Backend.Proof.StockMemoryLoadedPointerStoreRecord
import FV.Backend.Proof.StockMemoryStoreContract
import FV.Backend.Proof.IselMemRoots

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem source_width (kind : Kind) {ty : Clif.Ty}
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i value pointer : Nat} {info : IInfo} {flags : Clif.MemFlags}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.store kind.sourceOp ty flags value pointer 0)) : ty.width ≤ 64 := by
  cases ty <;> try decide
  have data := inv.data i info _ source clif
  cases kind <;> simp [instData,eTy,Kind.sourceOp] at data

/-- Actual retained store code writes source memory and preserves every virtual register after final alias resolution. -/
theorem stock_lower_loaded_pointer_store_record_run_of_store (kind : Kind) {ty : Clif.Ty}
    {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {value pointer valueReg pointerReg : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.store kind.sourceOp ty flags value pointer 0))
    (typed : kind.sourceOp = .store → event.ctx.valueType? value = some (.int kind.width.bits))
    {pointerInst sourcePointer : Nat} {pointerInfo : IInfo} {pointerFlags : Clif.MemFlags} {pointerOffset : Int}
    (pointerDefinition : event.ctx.defInst? pointer = some pointerInst)
    (pointerSource : event.ctx.insts[pointerInst]? = some pointerInfo)
    (pointerData : pointerInfo.data = .data 152 16
      [.data 151 29 [],.value sourcePointer,.op (.memFlags pointerFlags),.int pointerOffset])
    (pointerType : pointerInfo.resTys.head? = some (.int 64))
    (pointerMapped : event.ctx.valueReg? pointer = some (.vreg pointerReg .int))
    (valueMapped : event.ctx.valueReg? value = some (.vreg valueReg .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Backend.Proof.Sem}
    {MR : MemRelT} (stable : MRStable F MR) (memorySem : StoreRefines F sb isem)
    (memoryOk : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {ρ : Nat → CV} {cm cm' : Clif.Mem} {w : Arm.ArmState}
    (memory : MR fr.slots cm w) (dfg : DFGCons event.ctx fr)
    (pointerHeld : ValueHeld event.ctx fr (fun k => ρ (aliasNum result.final.alias k)) pointer)
    (valueHeld : ValueHeld event.ctx fr (fun k => ρ (aliasNum result.final.alias k)) value)
    {vals : List Clif.Val}
    (evaluated : Clif.evalInst fr cm (.store kind.sourceOp ty flags value pointer 0) = .ok (vals,cm')) :
    ∃ pv w',fr.regs pointer = some pv ∧
      seqRun isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
          some (.fall ρ w') ∧
      SameWorld F w' (Arm.write_mem_bytes kind.storeOp.bytes (BitVec.ofNat 64 (Clif.effAddr pv 0))
        ((lo64 (ρ (aliasNum result.final.alias valueReg))).setWidth (kind.storeOp.bytes * 8)) w) ∧
      MR fr.slots cm' w' ∧ vals = [] := by
  obtain ⟨_,_,_,_,_,code,_,_,_⟩ := stock_lower_loaded_pointer_store_record kind run scope events records
    source clif typed pointerDefinition pointerSource pointerData pointerType pointerMapped valueMapped recorded emitted
  have resolved : record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) =
      [.store kind.storeOp (.vreg (aliasNum result.final.alias valueReg) .int)
        (.unsignedOffset (.vreg (aliasNum result.final.alias pointerReg) .int) 0) flags] := by
    rw [code]
    change [MInst.store kind.storeOp
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg valueReg .int))
      (.unsignedOffset (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
        (.vreg pointerReg .int)) 0) flags] = _
    rw [resolve_vreg,resolve_vreg]
    rfl
  have inv := (stock_lower_record_context run scope events).1
  have little := (integer_store_source_data kind inv source clif).1
  obtain ⟨a,pv,getValue,getPointer,sizeBound,valid,empty,memoryEq⟩ := evalInst_store_inv little evaluated
  have size : kind.storeOp.bytes = kind.sourceOp.size ty := by
    cases kind <;> first
    | rfl
    | exact cond_store (typed rfl) rfl fr a dfg getValue
  have stored : ∀ a,fr.getAs value ty = .ok a →
      VHolds ⟨ty,a⟩ (ρ (aliasNum result.final.alias valueReg)) := by
    intro a found
    obtain ⟨n,mapped,held⟩ := valueHeld _ (getAs_ok found)
    have same : n = valueReg := by simpa using mapped.symm.trans valueMapped
    subst n
    exact held
  have pointerTy := inv.addr64 _ _ _ pointer source clif rfl
  have address := mapped_unsigned_address (sb := sb) (bytes := kind.storeOp.bytes) (w := w)
    pointerHeld pointerMapped dfg pointerTy (off := 0) (by cases kind <;> decide)
  obtain ⟨pv,w',pointer,executed,same,memory',empty⟩ := store_source_seqRun_of_store stable memorySem memoryOk memory
    (n := aliasNum result.final.alias valueReg)
    (am := .unsignedOffset (.vreg (aliasNum result.final.alias pointerReg) .int) 0)
    (by intro r member; exact ⟨_,List.mem_singleton.mp member⟩)
    (aop := kind.storeOp) (by cases kind <;> decide) size (source_width kind inv source clif) little stored
    (fun pv present => by simpa [amUses,amVregs,AMode.regs,amodeAddr] using address pv present) evaluated
  exact ⟨pv,w',pointer,by rwa [resolved],same,memory',empty⟩

/-- The original unguarded-memory interface remains available. -/
theorem stock_lower_loaded_pointer_store_record_run (kind : Kind) {ty : Clif.Ty}
    {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {value pointer valueReg pointerReg : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.store kind.sourceOp ty flags value pointer 0))
    (typed : kind.sourceOp = .store → event.ctx.valueType? value = some (.int kind.width.bits))
    {pointerInst sourcePointer : Nat} {pointerInfo : IInfo} {pointerFlags : Clif.MemFlags} {pointerOffset : Int}
    (pointerDefinition : event.ctx.defInst? pointer = some pointerInst)
    (pointerSource : event.ctx.insts[pointerInst]? = some pointerInfo)
    (pointerData : pointerInfo.data = .data 152 16
      [.data 151 29 [],.value sourcePointer,.op (.memFlags pointerFlags),.int pointerOffset])
    (pointerType : pointerInfo.resTys.head? = some (.int 64))
    (pointerMapped : event.ctx.valueReg? pointer = some (.vreg pointerReg .int))
    (valueMapped : event.ctx.valueReg? value = some (.vreg valueReg .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Backend.Proof.Sem}
    {MR : MemRelT} (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {ρ : Nat → CV} {cm cm' : Clif.Mem} {w : Arm.ArmState}
    (memory : MR fr.slots cm w) (dfg : DFGCons event.ctx fr)
    (pointerHeld : ValueHeld event.ctx fr (fun k => ρ (aliasNum result.final.alias k)) pointer)
    (valueHeld : ValueHeld event.ctx fr (fun k => ρ (aliasNum result.final.alias k)) value)
    {vals : List Clif.Val}
    (evaluated : Clif.evalInst fr cm (.store kind.sourceOp ty flags value pointer 0) = .ok (vals,cm')) :
    ∃ pv w',fr.regs pointer = some pv ∧
      seqRun isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
          some (.fall ρ w') ∧
      SameWorld F w' (Arm.write_mem_bytes kind.storeOp.bytes (BitVec.ofNat 64 (Clif.effAddr pv 0))
        ((lo64 (ρ (aliasNum result.final.alias valueReg))).setWidth (kind.storeOp.bytes * 8)) w) ∧
      MR fr.slots cm' w' ∧ vals = [] := by
  exact stock_lower_loaded_pointer_store_record_run_of_store kind run scope events records source clif typed
    pointerDefinition pointerSource pointerData pointerType pointerMapped valueMapped recorded emitted stable (store_refines_of_mem memorySem)
    memoryOk memory dfg pointerHeld valueHeld evaluated

end Backend.Stock.Memory.StoreRoots
