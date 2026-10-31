import FV.Backend.Proof.StockMemoryStoreSource

namespace Backend.Stock.Memory
open Backend.Proof Backend.Proof.Driver Backend Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- The guarded memory semantics writes the same source-width payload in two worlds.
The machine values and addressing operands can differ outside their source contracts. -/
theorem store_source_result_pairR
    {F Rd : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Sem} {MR : MemRelT} {f : Clif.Function}
    (stable : MRStable F MR) (memorySem : MemRefinesR Rd F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {cm cm' : Clif.Mem} {w other : Arm.ArmState}
    (memory : MR fr.slots cm w) (otherMemory : MR fr.slots cm other)
    {op : Clif.StoreOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {x p : Nat} {off : Int}
    {vals : List Clif.Val} {aop : Backend.StoreOp} {n : Nat} {am : AMode}
    {uses otherUses : List CV} {value otherValue : CV}
    (scalar : aop ≠ .fpuStore128) (size : aop.bytes = op.size ty)
    (width : ty.width ≤ 64) (little : fl.endianness ≠ some .big)
    (held : ∀ a,fr.getAs x ty = .ok a → VHolds ⟨ty,a⟩ value)
    (otherHeld : ∀ a,fr.getAs x ty = .ok a → VHolds ⟨ty,a⟩ otherValue)
    (address : ∀ pv,fr.regs p = some pv → amodeAddr sb am aop.bytes uses w =
      some (BitVec.ofNat 64 (Clif.effAddr pv off)))
    (otherAddress : ∀ pv,fr.regs p = some pv → amodeAddr sb am aop.bytes otherUses other =
      some (BitVec.ofNat 64 (Clif.effAddr pv off)))
    (source : Clif.evalInst fr cm (.store op ty fl x p off) = .ok (vals,cm')) :
    ∃ (a : BitVec ty.width) (pv : Clif.Val) (t t' : Arm.ArmState),fr.getAs x ty = .ok a ∧ fr.regs p = some pv ∧
      isem (.store aop (.vreg n .int) am fl) (value :: uses) w = some ([],t,.next) ∧
      isem (.store aop (.vreg n .int) am fl) (otherValue :: otherUses) other = some ([],t',.next) ∧
      SameWorld F t (Arm.write_mem_bytes aop.bytes (BitVec.ofNat 64 (Clif.effAddr pv off))
        (a.setWidth (aop.bytes * 8)) w) ∧
      SameWorld F t' (Arm.write_mem_bytes aop.bytes (BitVec.ofNat 64 (Clif.effAddr pv off))
        (a.setWidth (aop.bytes * 8)) other) ∧
      MR fr.slots cm' t ∧ MR fr.slots cm' t' ∧ vals = [] := by
  obtain ⟨a,pv,hax,hpv,hle,hvalid,rfl,rfl⟩ := evalInst_store_inv little source
  rw [← size] at hvalid hle ⊢
  have avoid : Avoids F aop.bytes (BitVec.ofNat 64 (Clif.effAddr pv off)) := by
    intro k hk
    rw [← BitVec.ofNat_add]
    exact (memoryOk.valid _ _ _ _ _ memory hvalid).2 k (by omega)
  have bounded : aop.bytes * 8 ≤ ty.width := by
    have : ty.bytes * 8 = ty.width := by cases ty <;> rfl
    omega
  obtain ⟨t,run,same⟩ := memorySem.2.1 aop n am fl value uses w _ scalar (address pv hpv) avoid
  obtain ⟨t',otherRun,otherSame⟩ := memorySem.2.1 aop n am fl otherValue otherUses other _ scalar
    (otherAddress pv hpv) avoid
  rw [← store_setWidth (held a hax) bounded width] at same
  rw [← store_setWidth (otherHeld a hax) bounded width] at otherSame
  have written := memoryOk.store _ _ _ _ _ (a.setWidth (aop.bytes * 8)) memory hvalid
  have otherWritten := memoryOk.store _ _ _ _ _ (a.setWidth (aop.bytes * 8)) otherMemory hvalid
  rw [← writeBits_setWidth _ aop.bytes a bounded] at written otherWritten
  exact ⟨a,pv,t,t',hax,hpv,run,otherRun,same,otherSame,
    stable _ _ _ _ same.toNF written,stable _ _ _ _ otherSame.toNF otherWritten,rfl⟩

end Backend.Stock.Memory
