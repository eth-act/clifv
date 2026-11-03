import FV.Backend.Proof.StockAcquirePartialPrefixPointer

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A successful original acquire executes without requiring its future source consumer to run. -/
theorem acquire_read_prefix_value_world {F : BitVec 64 → Prop} {sb : Nat}
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
        some ([ofX (raw.setWidth 64)],next,.next) ∧ MR fr.slots cm next ∧ SameWorld F next world := by
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
  exact ⟨raw,next,smallEq,sameMemory,executed,stable _ _ _ _ sameWorld.toNF memory,sameWorld⟩

/-- Earlier successful deferred reads execute before a later source fault without evaluating future consumers. -/
theorem acquire_read_prefix_run_world {F : BitVec 64 → Prop} {sb : Nat}
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
      (∀ key,key ≠ dest → nextRegs key = regs key) ∧ MR fr.slots cm nextWorld ∧ SameWorld F nextWorld world := by
  obtain ⟨raw,next,smallEq,sameMemory,executed,after,sameWorld⟩ := acquire_read_prefix_value_world stable memorySem memoryOk
    atomicType little pointerSource pointerType pointerHeld source memory
  let operands : Array Operand := #[⟨pointerReg,.int,.use,.early,.reg⟩,⟨dest,.int,.def,.late,.reg⟩]
  let finalRegs := vdefUpd operands [ofX (raw.setWidth 64)] regs
  refine ⟨raw,finalRegs,next,smallEq,sameMemory,?_,?_,?_,after,sameWorld⟩
  · exact seqRun_isem_one (operands_loadAcquire (CTy.ofClif sourceTy) dest pointerReg flags) executed rfl
  · simp [finalRegs,operands,vdefUpd,writeV,Operand.isDef,Operand.isEarly,Operand.isLate,upd]
  · intro key different
    exact vdefUpd_other (by simpa [operands,Operand.isDef] using different)

/-- A delayed successful source read executes at a later read-prefix state without a future consumer outcome. -/
theorem acquire_deferred_read_prefix_run_world {F : BitVec 64 → Prop} {sb : Nat}
    {syms : String → Option Nat} {isem : Backend.Proof.Sem} {MR : MemRelT} {f : Clif.Function}
    (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem) (memoryOk : MemRelOk F sb syms f MR)
    {producerFrame referenceFrame : Clif.Frame} {producerMem referenceMem : Clif.Mem}
    {pointerId dest pointerReg : Nat} {pointer small : Clif.Val} {sourceTy : Clif.Ty}
    (atomicType : eTy sourceTy = true) {flags : Clif.MemFlags} (little : flags.endianness ≠ some .big)
    (pointerSource : producerFrame.regs pointerId = some pointer) (pointerType : pointer.ty = .i64)
    (pointerKept : referenceFrame.regs pointerId = producerFrame.regs pointerId) (memorySame : referenceMem = producerMem)
    (source : Clif.evalInst producerFrame producerMem (.atomicLoad sourceTy flags pointerId) = .ok ([small],producerMem))
    {regs : Nat → CV} (pointerHeld : VHolds pointer (regs pointerReg))
    {world : Arm.ArmState} (memory : MR referenceFrame.slots referenceMem world) :
    ∃ (raw : BitVec sourceTy.width) (nextRegs : Nat → CV) (nextWorld : Arm.ArmState),small = ⟨sourceTy,raw⟩ ∧
      seqRun isem [.loadAcquire (CTy.ofClif sourceTy) (.vreg dest .int) (.vreg pointerReg .int) flags]
        regs world = some (.fall nextRegs nextWorld) ∧ nextRegs dest = ofX (raw.setWidth 64) ∧
      (∀ key,key ≠ dest → nextRegs key = regs key) ∧ MR referenceFrame.slots referenceMem nextWorld ∧ SameWorld F nextWorld world := by
  have pointerAtReference := pointerKept.trans pointerSource
  have sameLoad : Clif.evalInst referenceFrame producerMem (.atomicLoad sourceTy flags pointerId) =
      Clif.evalInst producerFrame producerMem (.atomicLoad sourceTy flags pointerId) := by
    simp only [Clif.evalInst,Clif.Frame.get,pointerKept]
  have movedLoad : Clif.evalInst referenceFrame referenceMem (.atomicLoad sourceTy flags pointerId) = .ok ([small],referenceMem) := by
    rw [memorySame,sameLoad]
    exact source
  obtain ⟨raw,nextRegs,nextWorld,smallEq,sameMemory,executed,value,other,after,sameWorld⟩ :=
    acquire_read_prefix_run_world stable memorySem memoryOk atomicType little pointerAtReference pointerType pointerHeld movedLoad memory
  exact ⟨raw,nextRegs,nextWorld,smallEq,executed,value,other,after,sameWorld⟩


end Backend.Stock.Proof.Acquire810
