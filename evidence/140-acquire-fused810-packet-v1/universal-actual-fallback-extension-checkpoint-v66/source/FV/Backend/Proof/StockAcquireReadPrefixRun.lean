import FV.Backend.Proof.StockAcquireEntryPrefixChunkRun

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A successful original acquire executes without requiring its future source consumer to run. -/
theorem acquire_read_prefix_value {F : BitVec 64 → Prop} {sb : Nat}
    {syms : String → Option Nat} {isem : Backend.Proof.Sem} {MR : MemRelT} {f : Clif.Function}
    (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem) (memoryOk : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {cm cm' : Clif.Mem} {p d nr : Nat} {pointer small : Clif.Val} {sourceTy : Clif.Ty}
    (atomicType : eTy sourceTy = true) {flags : Clif.MemFlags} (little : flags.endianness ≠ some .big)
    (pointerSource : fr.regs p = some pointer) (pointerType : pointer.ty = .i64)
    {use : CV} (pointerHeld : VHolds pointer use)
    (source : Clif.evalInst fr cm (.atomicLoad sourceTy flags p) = .ok ([small],cm'))
    {world : Arm.ArmState} (memory : MR fr.slots cm world) :
    ∃ (raw : BitVec sourceTy.width) (next : Arm.ArmState),small = ⟨sourceTy,raw⟩ ∧ cm' = cm ∧
      isem (.loadAcquire (CTy.ofClif sourceTy) (.vreg d .int) (.vreg nr .int) flags) [use] world =
        some ([ofX (raw.setWidth 64)],next,.next) ∧ MR fr.slots cm next := by
  obtain ⟨actual,raw,found,valid,read,values,sameMemory⟩ := evalInst_atomicLoad_inv little source
  have samePointer := Option.some.inj (pointerSource.symm.trans found)
  subst actual
  have smallEq := (List.cons.inj values).1
  have address : lo64 use = BitVec.ofNat 64 (Clif.effAddr pointer 0) :=
    (lo64_of_holds pointerHeld pointerType).trans (effAddr_zero pointer).symm
  obtain ⟨bound,free⟩ := memoryOk.valid _ _ _ _ _ memory valid
  have avoids : Avoids F (CTy.ofClif sourceTy).bytes (lo64 use) := by
    intro j bounded
    rw [address,← BitVec.ofNat_add]
    exact free j (by simpa only [ofClif_bytes atomicType] using bounded)
  obtain ⟨next,executed,sameWorld⟩ := memorySem.2.2.2.2.1 (CTy.ofClif sourceTy) d nr flags use world
    (atomTy_ofClif atomicType) avoids
  have bits := atom_read_eq atomicType read bound
    (fun j bounded byte present => memoryOk.bytes _ _ _ _ byte memory (valid_sub valid bounded) present)
  have bytes : raw.setWidth 64 =
      (Arm.read_mem_bytes (CTy.ofClif sourceTy).bytes (BitVec.ofNat 64 (Clif.effAddr pointer 0)) world).setWidth 64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j bounded
    simp only [BitVec.getLsbD_setWidth,bits]
  change isem (.loadAcquire (CTy.ofClif sourceTy) (.vreg d .int) (.vreg nr .int) flags) [use] world =
    some ([ofX ((Arm.read_mem_bytes (CTy.ofClif sourceTy).bytes (lo64 use) world).setWidth 64)],next,.next) at executed
  rw [address,← bytes] at executed
  exact ⟨raw,next,smallEq,sameMemory,executed,stable _ _ _ _ sameWorld.toNF memory⟩

/-- Earlier successful deferred reads execute before a later source fault without evaluating future consumers. -/
theorem acquire_read_prefix_run {F : BitVec 64 → Prop} {sb : Nat}
    {syms : String → Option Nat} {isem : Backend.Proof.Sem} {MR : MemRelT} {f : Clif.Function}
    (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem) (memoryOk : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {cm cm' : Clif.Mem} {p dest pointerReg : Nat} {pointer small : Clif.Val} {sourceTy : Clif.Ty}
    (atomicType : eTy sourceTy = true) {flags : Clif.MemFlags} (little : flags.endianness ≠ some .big)
    (pointerSource : fr.regs p = some pointer) (pointerType : pointer.ty = .i64)
    {regs : Nat → CV} (pointerHeld : VHolds pointer (regs pointerReg))
    (source : Clif.evalInst fr cm (.atomicLoad sourceTy flags p) = .ok ([small],cm'))
    {world : Arm.ArmState} (memory : MR fr.slots cm world) :
    ∃ (raw : BitVec sourceTy.width) (nextRegs : Nat → CV) (nextWorld : Arm.ArmState),small = ⟨sourceTy,raw⟩ ∧ cm' = cm ∧
      seqRun isem [.loadAcquire (CTy.ofClif sourceTy) (.vreg dest .int) (.vreg pointerReg .int) flags]
        regs world = some (.fall nextRegs nextWorld) ∧ nextRegs dest = ofX (raw.setWidth 64) ∧
      (∀ key,key ≠ dest → nextRegs key = regs key) ∧ MR fr.slots cm nextWorld := by
  obtain ⟨raw,next,smallEq,sameMemory,executed,after⟩ := acquire_read_prefix_value stable memorySem memoryOk
    atomicType little pointerSource pointerType pointerHeld source memory
  let operands : Array Operand := #[⟨pointerReg,.int,.use,.early,.reg⟩,⟨dest,.int,.def,.late,.reg⟩]
  let finalRegs := vdefUpd operands [ofX (raw.setWidth 64)] regs
  refine ⟨raw,finalRegs,next,smallEq,sameMemory,?_,?_,?_,after⟩
  · exact seqRun_isem_one (operands_loadAcquire (CTy.ofClif sourceTy) dest pointerReg flags) executed rfl
  · simp [finalRegs,operands,vdefUpd,writeV,Operand.isDef,Operand.isEarly,Operand.isLate,upd]
  · intro key different
    exact vdefUpd_other (by simpa [operands,Operand.isDef] using different)

end Backend.Stock.Proof.Acquire810
