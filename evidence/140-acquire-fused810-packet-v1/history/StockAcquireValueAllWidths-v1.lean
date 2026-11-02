import FV.Backend.Proof.StockAcquireValue

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Every admitted atomic width has the same acquire value after zero extension.
The source outcomes derive validity. The root must derive its width and flag facts internally. -/
theorem acquire_widened_value {F : BitVec 64 → Prop} {sb : Nat}
    {syms : String → Option Nat} {isem : Backend.Proof.Sem} {MR : MemRelT}
    {f : Clif.Function} (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {cm cm' cm'' : Clif.Mem} {p z d nr : Nat}
    {pointer small widened : Clif.Val} {sourceTy targetTy : Clif.Ty}
    (atomicType : eTy sourceTy = true) (fits : targetTy.width ≤ 64)
    {flags : Clif.MemFlags} (little : flags.endianness ≠ some .big)
    (pointerSource : fr.regs p = some pointer) (pointerType : pointer.ty = .i64)
    {use : CV} (pointerHeld : VHolds pointer use)
    (source : Clif.evalInst fr cm (.atomicLoad sourceTy flags p) = .ok ([small],cm'))
    (extension : Clif.evalInst (withValue fr z small) cm' (.extend .uextend targetTy z) =
      .ok ([widened],cm''))
    {world : Arm.ArmState} (memory : MR fr.slots cm world) :
    ∃ (raw : BitVec sourceTy.width) (next : Arm.ArmState),small = ⟨sourceTy,raw⟩ ∧
      cm' = cm ∧ cm'' = cm ∧ VHolds widened (ofX (raw.setWidth 64)) ∧
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
  obtain ⟨input,inputSource,grows,outputs,sameExtension⟩ := evalInst_uextend_ok extension
  have inputEq : input = small := by
    simpa [withValue] using Option.some.inj inputSource
  subst input
  have widenedEq := (List.cons.inj outputs).1
  refine ⟨raw,next,smallEq,sameMemory,sameExtension.trans sameMemory,?_,executed,
    stable _ _ _ _ sameWorld.toNF memory⟩
  rw [widenedEq,smallEq]
  change (ofX (raw.setWidth 64)).setWidth targetTy.width = raw.setWidth targetTy.width
  simp only [ofX,BitVec.setWidth_setWidth_of_le _ (show 64 ≤ 128 by decide),
    BitVec.setWidth_setWidth_of_le _ fits]

end Backend.Stock.Proof.Acquire810
