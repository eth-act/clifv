import FV.Backend.Proof.IselMemSem
import FV.Backend.Proof.StockMemoryContract
import FV.Backend.Proof.StockValues

/-! Source loads through a resolved machine address. This bridge deliberately
does not require the legacy identity value/register context. Actual Stock
selection and mapped operand availability discharge the address premise. -/
namespace Backend.Stock.Memory
open Backend.Proof Backend.Proof.Driver Backend Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- A successful source load and its selected machine load agree under the
existing memory/world premises, independently of source/register numbering. -/
theorem load_source_result
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Sem} {MR : MemRelT} {f : Clif.Function}
    (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {cm cm' : Clif.Mem} {w : Arm.ArmState}
    (memory : MR fr.slots cm w)
    {op : Clif.LoadOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {p : Nat} {off : Int}
    {vals : List Clif.Val} {aop : Backend.LoadOp} {d : Nat} {am : AMode}
    {uses : List CV}
    (scalar : aop ≠ .fpuLoad128) (size : aop.bytes = op.size ty)
    (signed : loadSigned aop = op.signed) (width : ty.width ≤ 64)
    (little : fl.endianness ≠ some .big)
    (address : ∀ pv, fr.regs p = some pv →
      amodeAddr sb am aop.bytes uses w = some (BitVec.ofNat 64 (Clif.effAddr pv off)))
    (source : Clif.evalInst fr cm (.load op ty fl p off) = .ok (vals, cm')) :
    ∃ w' out, isem (.load aop (.vreg d .int) am fl) uses w = some ([out], w', .next) ∧
      SameWorld F w' w ∧ MR fr.slots cm' w' ∧
      ∀ v ∈ vals, VHolds v out := by
  obtain ⟨pv, raw, hpv, hle, hvalid, hread, rfl, rfl⟩ := evalInst_load_inv little source
  obtain ⟨hA64, hF⟩ := memoryOk.valid _ _ _ _ _ memory hvalid
  have avoid : Avoids F aop.bytes (BitVec.ofNat 64 (Clif.effAddr pv off)) := by
    intro k hk
    rw [← BitVec.ofNat_add]
    exact hF k (by omega)
  obtain ⟨w', run, same⟩ := memorySem.1 aop d am fl uses w _ scalar (address pv hpv) avoid
  refine ⟨w', ofX (loadVal aop (BitVec.ofNat 64 (Clif.effAddr pv off)) w),
    run, same, stable _ _ _ _ same.toNF memory, ?_⟩
  intro v hv
  simp only [List.mem_singleton] at hv
  subst v
  have bits := readBits_getLsbD_eq (s := w) hread hA64
    (fun i hi b hb => memoryOk.bytes _ _ _ _ b memory (valid_sub hvalid hi) hb)
  have positive : 0 < op.size ty := by
    rw [← size]
    cases aop <;> simp [LoadOp.bytes] at scalar ⊢
  have bounded : 8 * op.size ty ≤ ty.width := by
    have : ty.bytes * 8 = ty.width := by cases ty <;> rfl
    omega
  have bits' : ∀ j, raw.getLsbD j =
      (Arm.read_mem_bytes aop.bytes (BitVec.ofNat 64 (Clif.effAddr pv off)) w).getLsbD j := by
    rw [size]
    exact bits
  simp only [loadVal]
  rw [signed]
  exact load_holds size bits' width bounded positive op.signed

/-- The memory bridge lifts to the actual one-instruction virtual-machine run
for every integer-vreg addressing mode, preserving all registers except its def. -/
theorem load_source_seqRun
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Sem} {MR : MemRelT} {f : Clif.Function}
    (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {ρ : Nat → CV} {cm cm' : Clif.Mem} {w : Arm.ArmState}
    (memory : MR fr.slots cm w)
    {op : Clif.LoadOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {p : Nat} {off : Int}
    {vals : List Clif.Val} {aop : Backend.LoadOp} {d : Nat} {am : AMode}
    (vregs : AmVregs am)
    (scalar : aop ≠ .fpuLoad128) (size : aop.bytes = op.size ty)
    (signed : loadSigned aop = op.signed) (width : ty.width ≤ 64)
    (little : fl.endianness ≠ some .big)
    (address : ∀ pv, fr.regs p = some pv →
      amodeAddr sb am aop.bytes (amUses am ρ) w =
        some (BitVec.ofNat 64 (Clif.effAddr pv off)))
    (source : Clif.evalInst fr cm (.load op ty fl p off) = .ok (vals,cm')) :
    ∃ ρ' w', seqRun isem [.load aop (.vreg d .int) am fl] ρ w = some (.fall ρ' w') ∧
      SameWorld F w' w ∧ MR fr.slots cm' w' ∧
      (∀ v ∈ vals, VHolds v (ρ' d)) ∧ (∀ k, k ≠ d → ρ' k = ρ k) := by
  obtain ⟨w',out,run,same,memory',values⟩ := load_source_result stable memorySem memoryOk memory
    (d := d) scalar size signed width little address source
  obtain ⟨ops,opsEq,uses,defs,update⟩ := (load_ops aop d vregs fl).ops
  rw [← uses ρ] at run
  have executed := seqRun_isem_one opsEq run (by rw [defs]; rfl)
  rw [update] at executed
  exact ⟨upd ρ d out,w',executed,same,memory',
    fun v member => by rw [upd_same]; exact values v member,
    fun k different => by simp only [upd,different,ite_false]⟩

/-- Scaled unsigned byte offsets, including the zero offset selected by actual
root1043, also need only the mapped pointer's source-available value. -/
theorem mapped_unsigned_address
    {ctx : Ctx} {fr : Clif.Frame} {ρ : Nat → CV} {p n sb bytes off : Nat}
    {w : Arm.ArmState}
    (held : Proof.ValueHeld ctx fr ρ p)
    (mapped : ctx.valueReg? p = some (.vreg n .int))
    (dfg : DFGCons ctx fr) (pointer : ctx.valueType? p = some (.int 64))
    (range : off % bytes = 0 ∧ off ≤ 4095 * bytes) :
    ∀ pv, fr.regs p = some pv →
      amodeAddr sb (.unsignedOffset (.vreg n .int) off) bytes [ρ n] w =
        some (BitVec.ofNat 64 (Clif.effAddr pv (off : Int))) := by
  intro pv source
  obtain ⟨m,hm,value⟩ := held pv source
  have equal : m = n := by simpa using hm.symm.trans mapped
  subst m
  simp only [amodeAddr,ite_eq_left range]
  rw [lo64_of_holds value (pv_i64 dfg pointer source)]
  rw [← BitVec.ofInt_natCast,← BitVec.ofInt_natCast,← BitVec.ofInt_add,effAddr_ofInt]

/-- The selected unscaled address uses only the demanded mapped pointer; no
assumption that every source value has already been materialized is needed. -/
theorem mapped_unscaled_address
    {ctx : Ctx} {fr : Clif.Frame} {ρ : Nat → CV} {p n sb bytes : Nat}
    {w : Arm.ArmState} {off : Int}
    (held : Proof.ValueHeld ctx fr ρ p)
    (mapped : ctx.valueReg? p = some (.vreg n .int))
    (dfg : DFGCons ctx fr) (pointer : ctx.valueType? p = some (.int 64))
    (range : -256 ≤ off ∧ off ≤ 255) :
    ∀ pv, fr.regs p = some pv →
      amodeAddr sb (.unscaled (.vreg n .int) off) bytes [ρ n] w =
        some (BitVec.ofNat 64 (Clif.effAddr pv off)) := by
  intro pv source
  obtain ⟨m, hm, value⟩ := held pv source
  have equal : m = n := by simpa using hm.symm.trans mapped
  subst m
  simp only [amodeAddr, ite_eq_left range]
  rw [lo64_of_holds value (pv_i64 dfg pointer source)]
  rw [← BitVec.ofInt_natCast, ← BitVec.ofInt_add, effAddr_ofInt]

/-- Execute the actual resolved load template, preserve every other virtual
register, and retain the source memory relation. Freshness is the existing
whole-driver alias bound, independent of source value IDs. -/
theorem mapped_unscaled_load
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Sem} {MR : MemRelT} {f : Clif.Function}
    (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR)
    {ctx : Ctx} {fr : Clif.Frame} {ρ : Nat → CV} {cm cm' : Clif.Mem} {w : Arm.ArmState}
    (memory : MR fr.slots cm w) {aliases : Array (Option Nat)} {p n d : Nat}
    (fresh : aliases.size ≤ d)
    (held : Proof.ValueHeld ctx fr (fun k => ρ (Proof.aliasNum aliases k)) p)
    (mapped : ctx.valueReg? p = some (.vreg n .int))
    (dfg : DFGCons ctx fr) (pointer : ctx.valueType? p = some (.int 64))
    {op : Clif.LoadOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {off : Int}
    {vals : List Clif.Val} {aop : Backend.LoadOp}
    (scalar : aop ≠ .fpuLoad128) (size : aop.bytes = op.size ty)
    (signed : loadSigned aop = op.signed) (width : ty.width ≤ 64)
    (little : fl.endianness ≠ some .big) (range : -256 ≤ off ∧ off ≤ 255)
    (source : Clif.evalInst fr cm (.load op ty fl p off) = .ok (vals,cm')) :
    ∃ ρ' w', seqRun isem
      [(MInst.load aop (.vreg d .int) (.unscaled (.vreg n .int) off) fl).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size + 1))] ρ w = some (.fall ρ' w') ∧
      SameWorld F w' w ∧ MR fr.slots cm' w' ∧
      (∀ v ∈ vals, VHolds v (ρ' d)) ∧ (∀ k, k ≠ d → ρ' k = ρ k) := by
  have address := mapped_unscaled_address (sb := sb) (bytes := aop.bytes) (w := w)
    held mapped dfg pointer range
  obtain ⟨w',out,run,same,memory',values⟩ := load_source_result stable memorySem memoryOk memory
    (d := d) (am := .unscaled (.vreg (Proof.aliasNum aliases n) .int) off)
    (uses := [ρ (Proof.aliasNum aliases n)])
    scalar size signed width little
    (fun pv hpv => by simpa only [amodeAddr] using address pv hpv) source
  have fixed : Proof.aliasNum aliases d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none fresh]
    rfl
  have destination : Backend.lowerFunction.resolve aliases (aliases.size + 1) (.vreg d .int) =
      .vreg d .int := by
    rw [resolve_vreg]
    change Reg.vreg (Proof.aliasNum aliases d) .int = _
    rw [fixed]
  have code : (.load aop (.vreg d .int) (.unscaled (.vreg n .int) off) fl : MInst).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size + 1)) =
      .load aop (.vreg d .int) (.unscaled (.vreg (Proof.aliasNum aliases n) .int) off) fl := by
    change MInst.load aop
      (Backend.lowerFunction.resolve aliases (aliases.size + 1) (.vreg d .int))
      (.unscaled (Backend.lowerFunction.resolve aliases (aliases.size + 1) (.vreg n .int)) off) fl = _
    rw [destination,resolve_vreg]
    rfl
  have operands := load_ops aop d
    (am := .unscaled (.vreg (Proof.aliasNum aliases n) .int) off)
    (by intro r member; exact ⟨_,List.mem_singleton.mp member⟩) fl
  obtain ⟨ops,opsEq,uses,defs,update⟩ := operands.ops
  have usesEq : vuses ops ρ = [ρ (Proof.aliasNum aliases n)] := uses ρ
  rw [← usesEq] at run
  have executed := seqRun_isem_one opsEq run (by rw [defs]; rfl)
  rw [update] at executed
  exact ⟨upd ρ d out,w',by simpa only [code] using executed,same,memory',
    fun v member => by rw [upd_same]; exact values v member,
    fun k different => by simp only [upd,different,ite_false]⟩

end Backend.Stock.Memory
