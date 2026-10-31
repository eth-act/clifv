import FV.Backend.Proof.StockMemoryLoad

namespace Backend.Stock.Memory
open Backend.Proof Backend.Proof.Driver Backend Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Source stores agree with the machine write without identity source/register numbering. -/
theorem store_source_result
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Sem} {MR : MemRelT} {f : Clif.Function}
    (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {cm cm' : Clif.Mem} {w : Arm.ArmState}
    (memory : MR fr.slots cm w)
    {op : Clif.StoreOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {x p : Nat} {off : Int}
    {vals : List Clif.Val} {aop : Backend.StoreOp} {n : Nat} {am : AMode}
    {uses : List CV} {value : CV}
    (scalar : aop ≠ .fpuStore128) (size : aop.bytes = op.size ty)
    (width : ty.width ≤ 64) (little : fl.endianness ≠ some .big)
    (held : ∀ a, fr.getAs x ty = .ok a → VHolds ⟨ty,a⟩ value)
    (address : ∀ pv, fr.regs p = some pv →
      amodeAddr sb am aop.bytes uses w = some (BitVec.ofNat 64 (Clif.effAddr pv off)))
    (source : Clif.evalInst fr cm (.store op ty fl x p off) = .ok (vals,cm')) :
    ∃ pv w', fr.regs p = some pv ∧
      isem (.store aop (.vreg n .int) am fl) (value :: uses) w = some ([],w',.next) ∧
      SameWorld F w' (Arm.write_mem_bytes aop.bytes (BitVec.ofNat 64 (Clif.effAddr pv off))
        ((lo64 value).setWidth (aop.bytes * 8)) w) ∧
      MR fr.slots cm' w' ∧ vals = [] := by
  obtain ⟨a,pv,hax,hpv,hle,hvalid,rfl,rfl⟩ := evalInst_store_inv little source
  rw [← size] at hvalid hle ⊢
  obtain ⟨_,outside⟩ := memoryOk.valid _ _ _ _ _ memory hvalid
  have avoid : Avoids F aop.bytes (BitVec.ofNat 64 (Clif.effAddr pv off)) := by
    intro k hk
    rw [← BitVec.ofNat_add]
    exact outside k (by omega)
  obtain ⟨w',run,same⟩ := memorySem.2.1 aop n am fl value uses w _ scalar (address pv hpv) avoid
  have bounded : aop.bytes * 8 ≤ ty.width := by
    have : ty.bytes * 8 = ty.width := by cases ty <;> rfl
    omega
  refine ⟨pv,w',hpv,run,same,stable _ _ _ _ same.toNF ?_,rfl⟩
  rw [writeBits_setWidth _ aop.bytes a bounded,store_setWidth (held a hax) bounded width]
  exact memoryOk.store _ _ _ _ _ _ memory hvalid

/-- A machine store keeps every virtual register and transports the updated source memory. -/
theorem store_source_seqRun
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Sem} {MR : MemRelT} {f : Clif.Function}
    (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {ρ : Nat → CV} {cm cm' : Clif.Mem} {w : Arm.ArmState}
    (memory : MR fr.slots cm w)
    {op : Clif.StoreOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {x p : Nat} {off : Int}
    {vals : List Clif.Val} {aop : Backend.StoreOp} {n : Nat} {am : AMode}
    (vregs : AmVregs am)
    (scalar : aop ≠ .fpuStore128) (size : aop.bytes = op.size ty)
    (width : ty.width ≤ 64) (little : fl.endianness ≠ some .big)
    (held : ∀ a, fr.getAs x ty = .ok a → VHolds ⟨ty,a⟩ (ρ n))
    (address : ∀ pv, fr.regs p = some pv →
      amodeAddr sb am aop.bytes (amUses am ρ) w =
        some (BitVec.ofNat 64 (Clif.effAddr pv off)))
    (source : Clif.evalInst fr cm (.store op ty fl x p off) = .ok (vals,cm')) :
    ∃ pv w', fr.regs p = some pv ∧
      seqRun isem [.store aop (.vreg n .int) am fl] ρ w = some (.fall ρ w') ∧
      SameWorld F w' (Arm.write_mem_bytes aop.bytes (BitVec.ofNat 64 (Clif.effAddr pv off))
        ((lo64 (ρ n)).setWidth (aop.bytes * 8)) w) ∧
      MR fr.slots cm' w' ∧ vals = [] := by
  obtain ⟨pv,w',pointer,run,same,memory',empty⟩ := store_source_result stable memorySem memoryOk memory
    (n := n) scalar size width little held address source
  obtain ⟨ops,opsEq,uses,defs,update⟩ := (store_ops aop n vregs fl).ops
  rw [← uses ρ] at run
  have executed := seqRun_isem_one opsEq run (by rw [defs]; rfl)
  rw [update] at executed
  exact ⟨pv,w',pointer,executed,same,memory',empty⟩

end Backend.Stock.Memory
