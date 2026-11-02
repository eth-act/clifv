import FV.Backend.Proof.StockAcquireHelpers
import FV.Backend.Proof.StockGuardedRecordValues

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The original atomic byte read supplies the exact widened acquire result.
Access validity is derived from source success, not added to accepted inputs. -/
theorem acquire_byte_widened_value {F : BitVec 64 → Prop} {sb : Nat}
    {syms : String → Option Nat} {isem : Backend.Proof.Sem} {MR : MemRelT}
    {f : Clif.Function} (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {cm cm' : Clif.Mem} {p z d nr : Nat} {pointer small : Clif.Val}
    {flags : Clif.MemFlags} (little : flags.endianness ≠ some .big)
    (pointerSource : fr.regs p = some pointer) (pointerType : pointer.ty = .i64)
    {use : CV} (pointerHeld : VHolds pointer use)
    (source : Clif.evalInst fr cm (.atomicLoad .i8 flags p) = .ok ([small],cm'))
    {world : Arm.ArmState} (memory : MR fr.slots cm world) :
    ∃ (raw : BitVec 8) (next : Arm.ArmState),small = ⟨.i8,raw⟩ ∧ cm' = cm ∧
      Clif.evalInst (withValue fr z small) cm' (.extend .uextend .i64 z) =
        .ok ([⟨.i64,raw.setWidth 64⟩],cm) ∧
      isem (.loadAcquire (.int 8) (.vreg d .int) (.vreg nr .int) flags) [use] world =
        some ([ofX (raw.setWidth 64)],next,.next) ∧ MR fr.slots cm next := by
  obtain ⟨actual,raw,found,valid,read,values,sameMemory⟩ := evalInst_atomicLoad_inv little source
  have samePointer := Option.some.inj (pointerSource.symm.trans found)
  subst actual
  have smallEq := (List.cons.inj values).1
  have address : lo64 use = BitVec.ofNat 64 (Clif.effAddr pointer 0) :=
    (lo64_of_holds pointerHeld pointerType).trans (effAddr_zero pointer).symm
  obtain ⟨bound,free⟩ := memoryOk.valid _ _ _ _ _ memory valid
  have avoids : Avoids F 1 (lo64 use) := by
    intro j bounded
    rw [address,← BitVec.ofNat_add]
    exact free j bounded
  obtain ⟨next,executed,sameWorld⟩ := memorySem.2.2.2.2.1 (.int 8) d nr flags use world
    (by simp [AtomTy]) avoids
  have bits := atom_read_eq (by decide : eTy .i8 = true) read bound
    (fun j bounded byte present => memoryOk.bytes _ _ _ _ byte memory (valid_sub valid bounded) present)
  have bytes : raw = Arm.read_mem_bytes 1 (BitVec.ofNat 64 (Clif.effAddr pointer 0)) world := by
    apply BitVec.eq_of_getLsbD_eq
    intro j bounded
    exact bits j
  rw [address,← bytes] at executed
  refine ⟨raw,next,smallEq,sameMemory,?_,executed,stable _ _ _ _ sameWorld.toNF memory⟩
  rw [smallEq,sameMemory]
  simp [Clif.evalInst,withValue,Clif.Frame.get,Clif.Res.check,Clif.Sem.uextend]

end Backend.Stock.Proof.Acquire810
