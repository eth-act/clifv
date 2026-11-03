import FV.Backend.Proof.StockAcquireReadPrefixWorld
import FV.E2E.DeadCleanupPair

namespace E2E.StockAcquirePair
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- A successful paired straight-line run retains both complete register files. -/
theorem seqRun_paired_fall_projections {isem : Backend.Proof.Sem} {code : List MInst}
    {regs next : Nat → CV} {left right nextLeft nextRight : Arm.ArmState}
    (run : seqRun (pairSem isem) code regs (left,right) = some (.fall next (nextLeft,nextRight))) :
    seqRun isem code regs left = some (.fall next nextLeft) ∧
      seqRun isem code regs right = some (.fall next nextRight) := by
  constructor
  · exact seqRun_mapW (P := fun _ => True) (π := Prod.fst)
      (fun _ _ _ _ _ _ _ h => (pairSem_inv h).1) code (by intros;trivial) regs (left,right) _ run
  · exact seqRun_mapW (P := fun _ => True) (π := Prod.snd)
      (fun _ _ _ _ _ _ _ h => (pairSem_inv h).2) code (by intros;trivial) regs (left,right) _ run

/-- Two original successful reads derive one paired acquire and the same complete virtual file. -/
theorem acquire_read_prefix_paired {F Z : BitVec 64 → Prop} {sb : Nat}
    {syms : String → Option Nat} {isem : Backend.Proof.Sem} {MR : MemRelT} {f : Clif.Function}
    (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem) (memoryOk : MemRelOk F sb syms f MR)
    (frame : ∀ a,F a → Z a)
    {fr : Clif.Frame} {cm cm' : Clif.Mem} {p dest pointerReg : Nat} {pointer small : Clif.Val} {sourceTy : Clif.Ty}
    (atomicType : eTy sourceTy = true) {flags : Clif.MemFlags} (little : flags.endianness ≠ some .big)
    (pointerSource : fr.regs p = some pointer) (pointerType : pointer.ty = .i64)
    {regs : Nat → CV} (pointerHeld : VHolds pointer (regs pointerReg))
    (source : Clif.evalInst fr cm (.atomicLoad sourceTy flags p) = .ok ([small],cm'))
    {left right : Arm.ArmState} (memoryLeft : MR fr.slots cm left) (memoryRight : MR fr.slots cm right)
    (worlds : SameWorld Z left right) :
    ∃ (raw : BitVec sourceTy.width) (nextRegs : Nat → CV) (nextLeft nextRight : Arm.ArmState),
      small = ⟨sourceTy,raw⟩ ∧ cm' = cm ∧
      seqRun (pairSem isem) [.loadAcquire (CTy.ofClif sourceTy) (.vreg dest .int) (.vreg pointerReg .int) flags]
        regs (left,right) = some (.fall nextRegs (nextLeft,nextRight)) ∧
      nextRegs dest = ofX (raw.setWidth 64) ∧ (∀ key,key ≠ dest → nextRegs key = regs key) ∧
      MR fr.slots cm nextLeft ∧ MR fr.slots cm nextRight ∧ SameWorld Z nextLeft nextRight := by
  obtain ⟨raw,nextLeft,smallEq,sameMemory,runLeft,afterLeft,keptLeft⟩ :=
    acquire_read_prefix_value_world stable memorySem memoryOk atomicType little pointerSource pointerType (d := dest) (nr := pointerReg) pointerHeld source memoryLeft
  obtain ⟨other,nextRight,otherEq,_,runRight,afterRight,keptRight⟩ :=
    acquire_read_prefix_value_world stable memorySem memoryOk atomicType little pointerSource pointerType (d := dest) (nr := pointerReg) pointerHeld source memoryRight
  have rawEq : raw = other := by
    have equal := smallEq.symm.trans otherEq
    cases equal
    rfl
  subst other
  let ops : Array Operand := #[⟨pointerReg,.int,.use,.early,.reg⟩,⟨dest,.int,.def,.late,.reg⟩]
  let updated := vdefUpd ops [ofX (raw.setWidth 64)] regs
  have paired := pairSem_eq (p := (left,right)) runLeft runRight
  have execution : seqRun (pairSem isem)
      [.loadAcquire (CTy.ofClif sourceTy) (.vreg dest .int) (.vreg pointerReg .int) flags]
      regs (left,right) = some (.fall updated (nextLeft,nextRight)) := by
    have operands : (MInst.loadAcquire (CTy.ofClif sourceTy) (.vreg dest .int) (.vreg pointerReg .int) flags).operands = .ok ops :=
      operands_loadAcquire (CTy.ofClif sourceTy) dest pointerReg flags
    have actual : pairSem isem (.loadAcquire (CTy.ofClif sourceTy) (.vreg dest .int) (.vreg pointerReg .int) flags)
        (vuses ops regs) (left,right) = some ([ofX (raw.setWidth 64)],(nextLeft,nextRight),.next) := paired
    simp only [seqRun,operands,actual]
    rfl
  refine ⟨raw,updated,nextLeft,nextRight,smallEq,sameMemory,execution,?_,?_,afterLeft,afterRight,?_⟩
  · simp [updated,ops,vdefUpd,writeV,Operand.isDef,Operand.isEarly,Operand.isLate,upd]
  · intro key different
    exact vdefUpd_other (by simpa [ops,Operand.isDef] using different)
  · exact SameWorld.trans (SameWorld.mono frame keptLeft)
      (SameWorld.trans worlds (SameWorld.symm (SameWorld.mono frame keptRight)))

end E2E.StockAcquirePair
