import FV.Backend.Proof.StockAcquirePositionedSourceValues
import FV.Backend.Proof.StockAcquireSelectedPairValue
import FV.Backend.Proof.StockAcquireReadPrefixPaired

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Derived source frames allow the real acquire value contract to execute a nonadjacent original pair. -/
theorem acquire_deferred_run_paired {F Z : BitVec 64 → Prop} {sb : Nat}
    {syms : String → Option Nat} {isem : Backend.Proof.Sem} {MR : MemRelT} {f : Clif.Function}
    (frame : ∀ a,F a → Z a) (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem) (memoryOk : MemRelOk F sb syms f MR)
    {producerFrame consumerFrame : Clif.Frame} {producerMem consumerMem nextMem : Clif.Mem}
    {pointerId valueId dest pointerReg : Nat} {pointer small widened : Clif.Val} {sourceTy targetTy : Clif.Ty}
    (atomicType : eTy sourceTy = true) (fits : targetTy.width ≤ 64)
    {flags : Clif.MemFlags} (little : flags.endianness ≠ some .big)
    (pointerSource : producerFrame.regs pointerId = some pointer) (pointerType : pointer.ty = .i64)
    (pointerKept : consumerFrame.regs pointerId = producerFrame.regs pointerId)
    (valueBound : consumerFrame.regs valueId = some small) (memorySame : consumerMem = producerMem)
    (source : Clif.evalInst producerFrame producerMem (.atomicLoad sourceTy flags pointerId) = .ok ([small],producerMem))
    (extension : Clif.evalInst consumerFrame consumerMem (.extend .uextend targetTy valueId) = .ok ([widened],nextMem))
    {regs : Nat → CV} (pointerHeld : VHolds pointer (regs pointerReg))
    {world otherWorld : Arm.ArmState} (memory : MR consumerFrame.slots consumerMem world)
    (otherMemory : MR consumerFrame.slots consumerMem otherWorld) (worlds : SameWorld Z world otherWorld) :
    ∃ nextRegs nextWorld nextOther,nextMem = consumerMem ∧
      seqRun (E2E.pairSem isem) [.loadAcquire (CTy.ofClif sourceTy) (.vreg dest .int) (.vreg pointerReg .int) flags]
        regs (world,otherWorld) = some (.fall nextRegs (nextWorld,nextOther)) ∧
      VHolds widened (nextRegs dest) ∧ (∀ key,key ≠ dest → nextRegs key = regs key) ∧
      MR consumerFrame.slots consumerMem nextWorld ∧ MR consumerFrame.slots consumerMem nextOther ∧
      SameWorld Z nextWorld nextOther := by
  have pointerAtConsumer := pointerKept.trans pointerSource
  have sameLoad : Clif.evalInst consumerFrame producerMem (.atomicLoad sourceTy flags pointerId) =
      Clif.evalInst producerFrame producerMem (.atomicLoad sourceTy flags pointerId) := by
    simp only [Clif.evalInst,Clif.Frame.get,pointerKept]
  have movedLoad : Clif.evalInst consumerFrame consumerMem (.atomicLoad sourceTy flags pointerId) = .ok ([small],consumerMem) := by
    rw [memorySame,sameLoad]
    exact source
  have sameExtension : Clif.evalInst (withValue consumerFrame valueId small) consumerMem (.extend .uextend targetTy valueId) =
      Clif.evalInst consumerFrame consumerMem (.extend .uextend targetTy valueId) := by
    apply Opt.evalInst_congr (fr := consumerFrame) (fr' := withValue consumerFrame valueId small)
      (mem := consumerMem) (i := .extend .uextend targetTy valueId) rfl rfl rfl
    intro value member
    have same : value = valueId := by simpa only [Opt.operands,List.mem_singleton] using member
    subst value
    simp [withValue,valueBound]
  have movedExtension : Clif.evalInst (withValue consumerFrame valueId small) consumerMem (.extend .uextend targetTy valueId) =
      .ok ([widened],nextMem) := sameExtension.trans extension
  obtain ⟨raw,nextRegs,nextWorld,nextOther,smallEq,_,executed,value,other,after,afterOther,pairedWorlds⟩ :=
    E2E.StockAcquirePair.acquire_read_prefix_paired stable memorySem memoryOk frame atomicType little
      pointerAtConsumer pointerType pointerHeld movedLoad memory otherMemory worlds
  obtain ⟨input,inputAt,width,outputs,extensionMemory⟩ := evalInst_uextend_ok extension
  have inputEq : input = small := (Option.some.inj (valueBound.symm.trans inputAt)).symm
  have widenedEq := (List.cons.inj outputs).1
  have held : VHolds widened (nextRegs dest) := by
    rw [value,widenedEq,inputEq,smallEq]
    change (ofX (raw.setWidth 64)).setWidth targetTy.width = raw.setWidth targetTy.width
    simp only [ofX]
    rw [BitVec.setWidth_setWidth_of_le _ (by omega : targetTy.width ≤ 128),
      BitVec.setWidth_setWidth_of_le _ fits]
  exact ⟨nextRegs,nextWorld,nextOther,extensionMemory,executed,held,other,after,afterOther,pairedWorlds⟩

end Backend.Stock.Proof.Acquire810
