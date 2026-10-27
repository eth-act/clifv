import FV.Backend.Proof.StockMemoryLoad

namespace Backend.Stock.Memory
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Both original memory/world relations fix every initialized byte read by a
successful source access, even where the surrounding worlds may differ. This
compares full canonical machine load values, rather than only source-width bits. -/
theorem initialized_load_value_eq
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {MR : MemRelT} {f : Clif.Function} (memoryOk : MemRelOk F sb syms f MR)
    {sl : List (Clif.SlotId × Nat)} {cm : Clif.Mem} {w w' : Arm.ArmState}
    (memory : MR sl cm w) (other : MR sl cm w')
    {a n : Nat} (valid : cm.valid a n = true) {raw : BitVec (8*n)}
    (read : cm.readBits false a n (8*n) = some raw)
    (op : LoadOp) (size : op.bytes = n) :
    loadVal op (BitVec.ofNat 64 a) w = loadVal op (BitVec.ofNat 64 a) w' := by
  subst n
  have bound := (memoryOk.valid _ _ _ _ _ memory valid).1
  have bits := readBits_getLsbD_eq (s := w) read bound
    (fun k hk b hb => memoryOk.bytes _ _ _ _ b memory (valid_sub valid hk) hb)
  have otherBits := readBits_getLsbD_eq (s := w') read bound
    (fun k hk b hb => memoryOk.bytes _ _ _ _ b other (valid_sub valid hk) hb)
  have equal : Arm.read_mem_bytes op.bytes (BitVec.ofNat 64 a) w =
      Arm.read_mem_bytes op.bytes (BitVec.ofNat 64 a) w' := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    exact (bits k).symm.trans (otherBits k)
  unfold loadVal
  rw [equal]

/-- Successful original loads execute the same exact machine output on both
related worlds. Memory validity and initialized bytes come from the original
source execution and the two original memory/world relations. -/
theorem load_source_result_pair
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Sem} {MR : MemRelT} {f : Clif.Function}
    (memorySem : MemRefines F sb syms isem) (memoryOk : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {cm cm' : Clif.Mem} {w w' : Arm.ArmState}
    (memory : MR fr.slots cm w) (other : MR fr.slots cm w')
    {op : Clif.LoadOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {p : Nat} {off : Int}
    {vals : List Clif.Val} {aop : LoadOp} {d : Nat} {am : AMode} {uses : List CV}
    (scalar : aop ≠ .fpuLoad128) (size : aop.bytes = op.size ty)
    (little : fl.endianness ≠ some .big)
    (address : ∀ pv,fr.regs p = some pv →
      amodeAddr sb am aop.bytes uses w = some (BitVec.ofNat 64 (Clif.effAddr pv off)))
    (otherAddress : ∀ pv,fr.regs p = some pv →
      amodeAddr sb am aop.bytes uses w' = some (BitVec.ofNat 64 (Clif.effAddr pv off)))
    (source : Clif.evalInst fr cm (.load op ty fl p off) = .ok (vals,cm')) :
    ∃ out t t',isem (.load aop (.vreg d .int) am fl) uses w = some ([out],t,.next) ∧
      isem (.load aop (.vreg d .int) am fl) uses w' = some ([out],t',.next) ∧
      SameWorld F t w ∧ SameWorld F t' w' := by
  obtain ⟨pv,raw,pointer,width,valid,read,valsEq,memEq⟩ := evalInst_load_inv little source
  have avoid : Avoids F aop.bytes (BitVec.ofNat 64 (Clif.effAddr pv off)) := by
    intro k hk
    rw [← BitVec.ofNat_add]
    exact (memoryOk.valid _ _ _ _ _ memory valid).2 k (by omega)
  obtain ⟨t,executed,same⟩ := memorySem.1 aop d am fl uses w _ scalar (address pv pointer) avoid
  obtain ⟨t',otherRun,otherSame⟩ := memorySem.1 aop d am fl uses w' _ scalar (otherAddress pv pointer) avoid
  have equal := initialized_load_value_eq memoryOk memory other valid read aop size
  rw [← equal] at otherRun
  exact ⟨_,t,t',executed,otherRun,same,otherSame⟩

/-- The same exact paired load proof applies to the existing guarded memory
semantics. Read permissions are derived from initialized source bytes, so the
legacy guarded lockstep/pairing framework can be reused. -/
theorem load_source_result_pairR
    {F Rd : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Sem} {MR : MemRelT} {f : Clif.Function}
    (memorySem : MemRefinesR Rd F sb syms isem) (memoryOk : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {cm cm' : Clif.Mem} {w w' : Arm.ArmState}
    (memory : MR fr.slots cm w) (other : MR fr.slots cm w') (reads : InitIn Rd cm)
    {op : Clif.LoadOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {p : Nat} {off : Int}
    {vals : List Clif.Val} {aop : LoadOp} {d : Nat} {am : AMode} {uses : List CV}
    (scalar : aop ≠ .fpuLoad128) (size : aop.bytes = op.size ty)
    (little : fl.endianness ≠ some .big)
    (address : ∀ pv,fr.regs p = some pv →
      amodeAddr sb am aop.bytes uses w = some (BitVec.ofNat 64 (Clif.effAddr pv off)))
    (otherAddress : ∀ pv,fr.regs p = some pv →
      amodeAddr sb am aop.bytes uses w' = some (BitVec.ofNat 64 (Clif.effAddr pv off)))
    (source : Clif.evalInst fr cm (.load op ty fl p off) = .ok (vals,cm')) :
    ∃ out t t',isem (.load aop (.vreg d .int) am fl) uses w = some ([out],t,.next) ∧
      isem (.load aop (.vreg d .int) am fl) uses w' = some ([out],t',.next) ∧
      SameWorld F t w ∧ SameWorld F t' w' := by
  obtain ⟨pv,raw,pointer,width,valid,read,valsEq,memEq⟩ := evalInst_load_inv little source
  have avoid : Avoids F aop.bytes (BitVec.ofNat 64 (Clif.effAddr pv off)) := by
    intro k hk
    rw [← BitVec.ofNat_add]
    exact (memoryOk.valid _ _ _ _ _ memory valid).2 k (by omega)
  have permitted : ∀ k < aop.bytes,Rd (BitVec.ofNat 64 (Clif.effAddr pv off)+BitVec.ofNat 64 k) := by
    intro k hk
    rw [← BitVec.ofNat_add]
    exact reads _ (valid_sub valid (by omega)) ((readBits_spec read).1 k (by omega))
  obtain ⟨t,executed,same⟩ := memorySem.1 aop d am fl uses w _ scalar (address pv pointer) avoid permitted
  obtain ⟨t',otherRun,otherSame⟩ := memorySem.1 aop d am fl uses w' _ scalar (otherAddress pv pointer) avoid permitted
  have equal := initialized_load_value_eq memoryOk memory other valid read aop size
  rw [← equal] at otherRun
  exact ⟨_,t,t',executed,otherRun,same,otherSame⟩

end Backend.Stock.Memory
