import FV.Backend.Proof.StockAcquireReadPrefixRun

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A delayed successful source read executes at a later read-prefix state without a future consumer outcome. -/
theorem acquire_deferred_read_prefix_run {F : BitVec 64 → Prop} {sb : Nat}
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
      (∀ key,key ≠ dest → nextRegs key = regs key) ∧ MR referenceFrame.slots referenceMem nextWorld := by
  have pointerAtReference := pointerKept.trans pointerSource
  have sameLoad : Clif.evalInst referenceFrame producerMem (.atomicLoad sourceTy flags pointerId) =
      Clif.evalInst producerFrame producerMem (.atomicLoad sourceTy flags pointerId) := by
    simp only [Clif.evalInst,Clif.Frame.get,pointerKept]
  have movedLoad : Clif.evalInst referenceFrame referenceMem (.atomicLoad sourceTy flags pointerId) = .ok ([small],referenceMem) := by
    rw [memorySame,sameLoad]
    exact source
  obtain ⟨raw,nextRegs,nextWorld,smallEq,sameMemory,executed,value,other,after⟩ :=
    acquire_read_prefix_run stable memorySem memoryOk atomicType little pointerAtReference pointerType pointerHeld movedLoad memory
  exact ⟨raw,nextRegs,nextWorld,smallEq,executed,value,other,after⟩

end Backend.Stock.Proof.Acquire810
