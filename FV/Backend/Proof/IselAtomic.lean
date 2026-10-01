import FV.Backend.Proof.IselMemFuncAddr
import FV.Backend.Proof.IselTls
import FV.Backend.Proof.IselCmpCond
import FV.Backend.Proof.IselFamAluBShiftTerms
import FV.Backend.Proof.IselCtlUnmatch
import FV.Backend.Proof.IselCmpRoot

/-!
# `bmask`, the atomics and `fence`

The root rules of `lower` for `bmask` (rule id 936, `lower_bmask`: `cmp #0` + `csetm ne`, an
8/16-bit value masked first), `fence` (1024, `dmb ish`), `atomic_load` (983, `ldar`),
`atomic_store` (984, `stlr`), `atomic_rmw` (994–1004, one per operation: the LL/SC
pseudo-instruction `AtomicRMWLoop`), `atomic_cas` (1007, `AtomicCASLoop`), and the `uextend` of
an `atomic_load` (810, never matches: `is_sinkable_inst` fails). `bmask` and `fence` are
`LowerRuleOk`; the atomics are memory rules (`MemRuleOk`, under `MemRefines`' atomic clauses).
The CLIF semantics is single-threaded (`Clif.evalInst`: a load, a store, or a load then a
store).

`memRulesCorrect_program` collects every memory root rule.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Helper terms -/

section Helpers
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

include hp hc in
/-- **`load_acquire`**: a fresh destination and `LoadAcquire`. -/
theorem load_acquire_ok {n : Nat} (hn : 40 ≤ n) {t flv a : V} {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 27 422 [t, flv, a] s v s') :
    ∃ m, MInst.ofV (.data 58 42 [t, .reg (s.1.fresh .int).1, a, flv]) = some m ∧
      v = .reg (s.1.fresh .int).1 ∧ s'.1 = (s.1.fresh .int).2.emit m := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 422
  mem_inv hp [] at hm he
  first | exact ⟨_, ‹_›, rfl, rfl⟩ | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›⟩

include hp hc in
/-- **`store_release`**: the `StoreRelease` as a side effect. -/
theorem store_release_ok {n : Nat} (hn : 40 ≤ n) {t flv x a : V} {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 46 423 [t, flv, x, a] s v s') :
    v = .data 46 0 [.data 58 43 [t, x, a, flv]] ∧ s'.1 = s.1 := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 423
  mem_inv hp [] at hm he

include hp hc in
/-- **`aarch64_fence`**: the `Fence` as a side effect. -/
theorem fence_helper_ok {n : Nat} (hn : 40 ≤ n) {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 46 466 [] s v s') :
    v = .data 46 0 [.data 58 44 []] ∧ s'.1 = s.1 := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 466
  mem_inv hp [] at hm he

set_option maxHeartbeats 2000000 in
include hp hc in
/-- **`atomic_rmw_loop`**: three fresh registers (old value, two scratch) and `AtomicRMWLoop`. -/
theorem atomic_rmw_loop_ok {n : Nat} (hn : 40 ≤ n) {o a x t flv : V}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 612 [o, a, x, t, flv] s v s') :
    ∃ m, MInst.ofV (.data 58 37 [t, o, flv, a, x, .reg (s.1.fresh .int).1,
        .reg ((s.1.fresh .int).2.fresh .int).1,
        .reg (((s.1.fresh .int).2.fresh .int).2.fresh .int).1]) = some m ∧
      v = .reg (s.1.fresh .int).1 ∧
      s'.1 = (((s.1.fresh .int).2.fresh .int).2.fresh .int).2.emit m := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 612
  mem_inv hp [] at hm he
  first | exact ⟨_, ‹_›, rfl, rfl⟩ | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›⟩

set_option maxHeartbeats 2000000 in
include hp hc in
/-- **`atomic_cas_loop`**: two fresh registers (old value, scratch) and `AtomicCASLoop`. -/
theorem atomic_cas_loop_ok {n : Nat} (hn : 40 ≤ n) {a e x t flv : V}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 613 [a, e, x, t, flv] s v s') :
    ∃ m, MInst.ofV (.data 58 38 [t, flv, a, e, x, .reg (s.1.fresh .int).1,
        .reg ((s.1.fresh .int).2.fresh .int).1]) = some m ∧
      v = .reg (s.1.fresh .int).1 ∧ s'.1 = ((s.1.fresh .int).2.fresh .int).2.emit m := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 613
  mem_inv hp [] at hm he
  first | exact ⟨_, ‹_›, rfl, rfl⟩ | exact ⟨_, ‹_›, rfl⟩ | exact ⟨_, ‹_›⟩

include hp hc in
/-- **`csetm`**: a fresh destination and `CSetm` (a consumer returning the register). -/
theorem csetm_ok {n : Nat} (hn : 40 ≤ n) {c : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 49 428 [c] s v s') :
    s'.1 = (s.1.fresh .int).2 ∧
      v = .data 49 3 [.data 58 34 [.reg (s.1.fresh .int).1, c], .reg (s.1.fresh .int).1] := by
  obtain ⟨st, tr⟩ := s
  mem_split hp hc h 428
  mem_inv hp [] at hm he

theorem ofV_csetm (rd : Reg) (c : V) :
    MInst.ofV (.data 58 34 [.reg rd, c]) = c.cond?.map (.csetm rd) := by
  have e1 : MInst.ofV (.data 58 34 [.reg rd, c]) = (do return .csetm rd (← c.cond?)) := rfl
  rw [e1]; cases c.cond? <;> rfl

set_option maxHeartbeats 2000000 in
include hp hc in
/-- **`with_flags_reg`**: emit the producer and the consumer, return the consumer's register. -/
theorem with_flags_reg_ok {n : Nat} (hn : 50 ≤ n) {mi ci : V} {r : Reg}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 255 [.data 47 1 [mi], .data 49 3 [ci, .reg r]] s v s') :
    ∃ m1 m2, MInst.ofV mi = some m1 ∧ MInst.ofV ci = some m2 ∧ v = .reg r ∧
      s'.1 = (s.1.emit m1).emit m2 := by
  isel_split' hp hc h 255
  all_goals isel_inv' hp [] at hm he
  all_goals isel_call hp hc [with_flags_ok]
  all_goals isel_inv_simp [Int.toNat_zero, List.getElem?_cons_zero, Option.some.injEq] at *
  all_goals isel_destruct
  all_goals subst_vars
  all_goals exact ⟨_, ‹_›, _, ‹_›, rfl, ‹_›⟩

set_option maxHeartbeats 4000000 in
include hp hc in
/-- **`lower_bmask`** from a 32- or 64-bit value: `cmp #0`, `csetm ne` into a fresh register. -/
theorem lower_bmask_3264_ok {n : Nat} (hn : 100 ≤ n) {wo wi : Nat} {r : Reg}
    (ho : wo ≤ 64) (hi : wi = 32 ∨ wi = 64) {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 22 658 [.ty (.int wo), .ty (.int wi), .regs [r]] s v s') :
    v = .regs [(s.1.fresh .int).1] ∧
      s'.1 = ((s.1.fresh .int).2.emit (.aluRRImm12 .subS (szOf wi) .xzr r ⟨0, false⟩)).emit
        (.csetm (s.1.fresh .int).1 .ne) := by
  rcases hi with rfl | rfl <;>
  isel_split' hp hc h 658
  all_goals try (mem_refute hp [CTy.bits] at hm; done)
  all_goals try (mem_refute hp [CTy.bits, CTy.int.injEq] at hm; omega)
  all_goals isel_inv' hp [CTy.bits] at hm he
  all_goals try (simp only [CTy.int.injEq] at *; omega)
  all_goals isel_call hp hc [operand_size_ok, cmp_imm_ok, csetm_ok, with_flags_reg_ok]
  all_goals isel_inv_simp [CTy.bits, Int.toNat_zero, List.getElem?_cons_zero, Option.some.injEq,
    ctor_u8_into_imm12_0, or_false, false_or, ofV_cmpImm, ofV_csetm, V.cond?_data, cond_ofIdx_1,
    Option.map_some, Option.map_eq_some_iff] at *
  all_goals isel_destruct
  all_goals subst_vars
  all_goals simp only [ofV_cmpImm, Option.map_eq_some_iff] at *
  all_goals isel_destruct
  all_goals subst_vars
  all_goals refine ⟨by simp_all, ?_⟩
  all_goals simp_all [szOf, OperandSize.ofIdx?]

theorem ctor_ty_mask_iff (st : LState) (w : Nat) (v : V) (st' : LState) :
    externCtor ctx T.ty_mask [.ty (.int w)] st = .ok (v, st') ↔ v = .int (2 ^ w - 1) ∧ st' = st := by
  have : externCtor ctx T.ty_mask [.ty (.int w)] st = .ok (.int (2 ^ w - 1), st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_imm_logic_255_iff (st : LState) (v : V) (st' : LState) :
    externCtor ctx T.imm_logic_from_u64 [.ty (.int 32), .int (2 ^ 8 - 1)] st = .ok (v, st') ↔
      v = .op (.immLogic ⟨255, .size32⟩) ∧ st' = st := by
  have : externCtor ctx T.imm_logic_from_u64 [.ty (.int 32), .int (2 ^ 8 - 1)] st =
    .ok (.op (.immLogic ⟨255, .size32⟩), st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_imm_logic_65535_iff (st : LState) (v : V) (st' : LState) :
    externCtor ctx T.imm_logic_from_u64 [.ty (.int 32), .int (2 ^ 16 - 1)] st = .ok (v, st') ↔
      v = .op (.immLogic ⟨65535, .size32⟩) ∧ st' = st := by
  have : externCtor ctx T.imm_logic_from_u64 [.ty (.int 32), .int (2 ^ 16 - 1)] st =
    .ok (.op (.immLogic ⟨65535, .size32⟩), st) := rfl
  rw [this]; simp [eq_comm]

set_option maxHeartbeats 4000000 in
include hp hc in
/-- **`lower_bmask`** from an 8- or 16-bit value: mask it (`and #ty_mask`), then as from 32 bits. -/
theorem lower_bmask_816_ok {n : Nat} (hn : 200 ≤ n) {wo wi : Nat} {r : Reg}
    (ho : wo ≤ 64) (hi : wi = 8 ∨ wi = 16) {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 22 658 [.ty (.int wo), .ty (.int wi), .regs [r]] s v s') :
    v = .regs [(((s.1.fresh .int).2.emit (.aluRRImmLogic .and .size32 (s.1.fresh .int).1 r
        ⟨2 ^ wi - 1, .size32⟩)).fresh .int).1] ∧
      s'.1 = (((((s.1.fresh .int).2.emit (.aluRRImmLogic .and .size32 (s.1.fresh .int).1 r
        ⟨2 ^ wi - 1, .size32⟩)).fresh .int).2.emit
          (.aluRRImm12 .subS .size32 .xzr (s.1.fresh .int).1 ⟨0, false⟩)).emit
        (.csetm (((s.1.fresh .int).2.emit (.aluRRImmLogic .and .size32 (s.1.fresh .int).1 r
          ⟨2 ^ wi - 1, .size32⟩)).fresh .int).1 .ne)) := by
  rcases hi with rfl | rfl <;>
  isel_split' hp hc h 658
  all_goals try (mem_refute hp [CTy.bits] at hm; done)
  all_goals try (mem_refute hp [CTy.bits, CTy.int.injEq] at hm; omega)
  all_goals isel_inv' hp [CTy.bits] at hm he
  all_goals try (simp only [CTy.int.injEq] at *; omega)
  all_goals try (simp only [Bool.or_self, Bool.false_eq_true] at *; done)
  all_goals isel_inv_simp [CTy.bits, Int.toNat_zero, List.getElem?_cons_zero, Option.some.injEq,
    ctor_ty_mask_iff, ctor_imm_logic_255_iff, ctor_imm_logic_65535_iff] at *
  all_goals isel_destruct
  all_goals subst_vars
  all_goals isel_call hp hc [and_imm_ok]
  all_goals repeat (isel_inv_simp [CTy.bits, ctor_imm_logic_255_iff, ctor_imm_logic_65535_iff,
    EmitOut, OSz, ofV_aluRRImmLogic_and_32, ctor_value_reg', or_false] at * <;> isel_destruct <;>
    subst_vars)
  all_goals
    have hrec := ‹ApplyInternal _ _ _ _ 22 658 _ _ _ _›
    obtain ⟨rfl, hs⟩ := lower_bmask_3264_ok hp hc (by omega) ho (.inl rfl) hrec
  all_goals simp_all [szOf]

end Helpers

/-! ## Instruction data of the root instructions -/

theorem atom_vn_LoadNoOffset : (variantNames 152)[17]? = some "LoadNoOffset" := rfl
theorem atom_vn_StoreNoOffset : (variantNames 152)[23]? = some "StoreNoOffset" := rfl
theorem atom_vn_AtomicRmwF : (variantNames 152)[1]? = some "AtomicRmw" := rfl
theorem atom_vn_AtomicCasF : (variantNames 152)[0]? = some "AtomicCas" := rfl
theorem atom_vn_Unary : (variantNames 152)[29]? = some "Unary" := rfl
theorem atom_vn_NullAry : (variantNames 152)[19]? = some "NullAry" := rfl
theorem atom_vn_AtomicLoad : (variantNames 151)[158]? = some "AtomicLoad" := rfl
theorem atom_vn_AtomicStore : (variantNames 151)[159]? = some "AtomicStore" := rfl
theorem atom_vn_AtomicRmw : (variantNames 151)[156]? = some "AtomicRmw" := rfl
theorem atom_vn_AtomicCas : (variantNames 151)[157]? = some "AtomicCas" := rfl
theorem atom_vn_Bmask : (variantNames 151)[130]? = some "Bmask" := rfl
theorem atom_vn_Fence : (variantNames 151)[160]? = some "Fence" := rfl

/-! ## The CLIF side -/

theorem evalInst_atomicLoad_inv {fr : Clif.Frame} {cm cm' : Clif.Mem} {ty : Clif.Ty}
    {fl : Clif.MemFlags} {p : Nat} {vals : List Clif.Val} (hfl : fl.endianness ≠ some .big)
    (h : Clif.evalInst fr cm (.atomicLoad ty fl p) = .ok (vals, cm')) :
    ∃ pv raw, fr.regs p = some pv ∧ cm.valid (Clif.effAddr pv 0) ty.bytes = true ∧
      cm.readBits false (Clif.effAddr pv 0) ty.bytes ty.width = some raw ∧
      vals = [⟨ty, raw⟩] ∧ cm' = cm := by
  simp only [Clif.evalInst] at h
  obtain ⟨pv, hpv, h⟩ := res_bind_eq_ok h
  obtain ⟨_, -, h⟩ := res_bind_eq_ok h
  obtain ⟨raw, hl, h⟩ := res_bind_eq_ok h
  simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq, Prod.mk.injEq] at h
  unfold Clif.Mem.load at hl
  obtain ⟨_, hca, hl⟩ := res_bind_eq_ok hl
  rw [big_false hfl] at hl
  exact ⟨pv, raw, get_regs hpv, checkAccess_ok hca, res_ofOption_ok hl, h.1.symm, h.2.symm⟩

theorem evalInst_atomicStore_inv {fr : Clif.Frame} {cm cm' : Clif.Mem} {ty : Clif.Ty}
    {fl : Clif.MemFlags} {x p : Nat} {vals : List Clif.Val} (hfl : fl.endianness ≠ some .big)
    (h : Clif.evalInst fr cm (.atomicStore ty fl x p) = .ok (vals, cm')) :
    ∃ a pv, fr.getAs x ty = .ok a ∧ fr.regs p = some pv ∧
      cm.valid (Clif.effAddr pv 0) ty.bytes = true ∧ vals = [] ∧
      cm' = cm.writeBits false (Clif.effAddr pv 0) ty.bytes a := by
  simp only [Clif.evalInst] at h
  obtain ⟨a, ha, h⟩ := res_bind_eq_ok h
  obtain ⟨pv, hpv, h⟩ := res_bind_eq_ok h
  obtain ⟨_, -, h⟩ := res_bind_eq_ok h
  obtain ⟨m', hs, h⟩ := res_bind_eq_ok h
  simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq, Prod.mk.injEq] at h
  unfold Clif.Mem.store at hs
  obtain ⟨_, hca, hs⟩ := res_bind_eq_ok hs
  obtain ⟨_, -, hs⟩ := res_bind_eq_ok hs
  rw [big_false hfl] at hs
  simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq] at hs
  exact ⟨a, pv, ha, get_regs hpv, checkAccess_ok hca, h.1.symm, h.2.symm.trans hs.symm⟩

theorem evalInst_atomicRmw_inv {fr : Clif.Frame} {cm cm' : Clif.Mem} {op : Clif.AtomicRmwOp}
    {ty : Clif.Ty} {fl : Clif.MemFlags} {p x : Nat} {vals : List Clif.Val}
    (hfl : fl.endianness ≠ some .big)
    (h : Clif.evalInst fr cm (.atomicRmw op ty fl p x) = .ok (vals, cm')) :
    ∃ pv a old, fr.regs p = some pv ∧ fr.getAs x ty = .ok a ∧
      cm.valid (Clif.effAddr pv 0) ty.bytes = true ∧
      cm.readBits false (Clif.effAddr pv 0) ty.bytes ty.width = some old ∧ vals = [⟨ty, old⟩] ∧
      cm' = cm.writeBits false (Clif.effAddr pv 0) ty.bytes (Clif.Sem.atomicRmw op old a) := by
  simp only [Clif.evalInst] at h
  obtain ⟨pv, hpv, h⟩ := res_bind_eq_ok h
  obtain ⟨a, ha, h⟩ := res_bind_eq_ok h
  obtain ⟨_, -, h⟩ := res_bind_eq_ok h
  obtain ⟨old, hl, h⟩ := res_bind_eq_ok h
  obtain ⟨m', hs, h⟩ := res_bind_eq_ok h
  simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq, Prod.mk.injEq] at h
  unfold Clif.Mem.load at hl
  obtain ⟨_, hca, hl⟩ := res_bind_eq_ok hl
  rw [big_false hfl] at hl
  unfold Clif.Mem.store at hs
  obtain ⟨_, -, hs⟩ := res_bind_eq_ok hs
  obtain ⟨_, -, hs⟩ := res_bind_eq_ok hs
  rw [big_false hfl] at hs
  simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq] at hs
  exact ⟨pv, a, old, get_regs hpv, ha, checkAccess_ok hca, res_ofOption_ok hl, h.1.symm,
    h.2.symm.trans hs.symm⟩

theorem evalInst_atomicCas_inv {fr : Clif.Frame} {cm cm' : Clif.Mem} {ty : Clif.Ty}
    {fl : Clif.MemFlags} {p e x : Nat} {vals : List Clif.Val} (hfl : fl.endianness ≠ some .big)
    (h : Clif.evalInst fr cm (.atomicCas ty fl p e x) = .ok (vals, cm')) :
    ∃ pv ev a old, fr.regs p = some pv ∧ fr.getAs e ty = .ok ev ∧ fr.getAs x ty = .ok a ∧
      cm.valid (Clif.effAddr pv 0) ty.bytes = true ∧
      cm.readBits false (Clif.effAddr pv 0) ty.bytes ty.width = some old ∧ vals = [⟨ty, old⟩] ∧
      cm' = if old = ev then cm.writeBits false (Clif.effAddr pv 0) ty.bytes a else cm := by
  simp only [Clif.evalInst] at h
  obtain ⟨pv, hpv, h⟩ := res_bind_eq_ok h
  obtain ⟨ev, he, h⟩ := res_bind_eq_ok h
  obtain ⟨a, ha, h⟩ := res_bind_eq_ok h
  obtain ⟨_, -, h⟩ := res_bind_eq_ok h
  obtain ⟨old, hl, h⟩ := res_bind_eq_ok h
  unfold Clif.Mem.load at hl
  obtain ⟨_, hca, hl⟩ := res_bind_eq_ok hl
  rw [big_false hfl] at hl
  refine ⟨pv, ev, a, old, get_regs hpv, he, ha, checkAccess_ok hca, res_ofOption_ok hl, ?_⟩
  by_cases heq : old = ev
  · have hb : (old == ev) = true := by simpa using heq
    rw [if_pos hb] at h
    obtain ⟨m', hs, h⟩ := res_bind_eq_ok h
    simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq, Prod.mk.injEq] at h
    unfold Clif.Mem.store at hs
    obtain ⟨_, -, hs⟩ := res_bind_eq_ok hs
    obtain ⟨_, -, hs⟩ := res_bind_eq_ok hs
    rw [big_false hfl] at hs
    simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq] at hs
    refine ⟨h.1.symm, ?_⟩
    rw [if_pos heq, ← h.2, ← hs]
  · have hb : (old == ev) = false := by simpa using heq
    rw [if_neg (by simp [hb])] at h
    simp only [pure, bind, Clif.Res.bind, Clif.Res.ok.injEq, Prod.mk.injEq] at h
    refine ⟨h.1.symm, ?_⟩
    rw [if_neg heq, ← h.2]

/-! ## The Arm side: loaded bytes -/

theorem eTy_cases {ty : Clif.Ty} (h : eTy ty = true) :
    ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64 := by
  cases ty <;> simp_all [eTy]

theorem atomTy_ofClif {ty : Clif.Ty} (h : eTy ty = true) : AtomTy (CTy.ofClif ty) := by
  rcases eTy_cases h with rfl | rfl | rfl | rfl <;> simp [AtomTy, CTy.ofClif]

/-- The bytes an atomic access reads, as the CLIF value of the access type. -/
theorem atom_read_eq {ty : Clif.Ty} (hety : eTy ty = true) {cm : Clif.Mem} {A : Nat}
    {raw : BitVec ty.width} {s : Arm.ArmState}
    (h : cm.readBits false A ty.bytes ty.width = some raw) (hA : A + ty.bytes ≤ 2 ^ 64)
    (hb : ∀ i < ty.bytes, ∀ b, cm.bytes (A + i) = some b →
      Arm.read_mem (BitVec.ofNat 64 (A + i)) s = b) :
    ∀ j, raw.getLsbD j =
      (Arm.read_mem_bytes (CTy.ofClif ty).bytes (BitVec.ofNat 64 A) s).getLsbD j := by
  rcases eTy_cases hety with rfl | rfl | rfl | rfl
  · exact readBits_getLsbD_eq (n := 1) h hA hb
  · exact readBits_getLsbD_eq (n := 2) h hA hb
  · exact readBits_getLsbD_eq (n := 4) h hA hb
  · exact readBits_getLsbD_eq (n := 8) h hA hb

/-- The loaded value, zero-extended into a register, holds the CLIF value. -/
theorem atom_holds {ty : Clif.Ty} (hety : eTy ty = true) {raw : BitVec ty.width} {n : Nat}
    {R : BitVec (n * 8)} (hn : n * 8 = ty.width) (hbits : ∀ j, raw.getLsbD j = R.getLsbD j) :
    VHolds ⟨ty, raw⟩ (ofX (R.setWidth 64)) := by
  simp only [VHolds]
  have hw := eTy_width hety
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, getLsbD_ofX, hbits]
  have : i < 64 := by omega
  simp [hi, this, show i < n * 8 by omega]

/-! ## The builders -/

theorem effAddr_zero (pv : Clif.Val) : BitVec.ofNat 64 (Clif.effAddr pv 0) = BitVec.ofNat 64 pv.toNat := by
  rw [← effAddr_ofInt]
  apply BitVec.eq_of_toNat_eq
  simp

theorem ofClif_bytes {ty : Clif.Ty} (h : eTy ty = true) : (CTy.ofClif ty).bytes = ty.bytes := by
  rcases eTy_cases h with rfl | rfl | rfl | rfl <;> rfl

theorem ofClif_bytes_width {ty : Clif.Ty} (h : eTy ty = true) : (CTy.ofClif ty).bytes * 8 = ty.width := by
  rcases eTy_cases h with rfl | rfl | rfl | rfl <;> rfl

theorem operands_loadAcquire (t : CTy) (d a : Nat) (fl : Clif.MemFlags) :
    (MInst.loadAcquire t (.vreg d .int) (.vreg a .int) fl).operands =
      .ok #[⟨a, .int, .use, .early, .reg⟩, ⟨d, .int, .def, .late, .reg⟩] := rfl

theorem operands_storeRelease (t : CTy) (x a : Nat) (fl : Clif.MemFlags) :
    (MInst.storeRelease t (.vreg x .int) (.vreg a .int) fl).operands =
      .ok #[⟨a, .int, .use, .early, .reg⟩, ⟨x, .int, .use, .early, .reg⟩] := rfl

/-- The address of an atomic access: the `i64` address value's register, its bytes outside the
frame addresses (`MemRelOk.valid`). -/
theorem atom_addr {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {f : Clif.Function}
    {MR : MemRelT} (hMRo : MemRelOk F sb syms f MR) {ctx : Ctx} {fr : Clif.Frame}
    (hdfg : DFGCons ctx fr) {ρ : Nat → CV} (hv : ValsHeld fr ρ) {p : Nat} {pv : Clif.Val}
    (hp64 : ctx.valueType? p = some (.int 64)) (hpv : fr.regs p = some pv) {sl : List (Clif.SlotId × Nat)}
    {cm : Clif.Mem} {w : Arm.ArmState} (hmr : MR sl cm w) {n : Nat}
    (hvalid : cm.valid (Clif.effAddr pv 0) n = true) :
    lo64 (ρ p) = BitVec.ofNat 64 (Clif.effAddr pv 0) ∧ Clif.effAddr pv 0 + n ≤ 2 ^ 64 ∧
      Avoids F n (lo64 (ρ p)) := by
  have ha : lo64 (ρ p) = BitVec.ofNat 64 (Clif.effAddr pv 0) := by
    rw [effAddr_zero]; exact lo64_of_holds (hv p pv hpv) (pv_i64 hdfg hp64 hpv)
  obtain ⟨hA64, hF⟩ := hMRo.valid _ _ _ _ _ hmr hvalid
  refine ⟨ha, hA64, fun k hk => ?_⟩
  rw [ha, ← BitVec.ofNat_add]
  exact hF k hk

section Builders
variable {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Sem}
  {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} {f : Clif.Function} {ctx : Ctx}

/-- **`atomic_load`**: `ldar` of the address register into a fresh register. -/
theorem atomicLoad_lower_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem)
    (hMRo : MemRelOk F sb syms f MR) {st : LState} {ty : Clif.Ty} {fl : Clif.MemFlags}
    {p : Nat} {results : List Nat} (hety : eTy ty = true) (hfl : fl.endianness ≠ some .big)
    (hp64 : ctx.valueType? p = some (.int 64)) :
    LowerInstOk isem MR env cp ctx (.atomicLoad ty fl p) results st [[(st.fresh .int).1]]
      ((st.fresh .int).2.emit (.loadAcquire (CTy.ofClif ty) (st.fresh .int).1 (.vreg p .int) fl))
      [.loadAcquire (CTy.ofClif ty) (st.fresh .int).1 (.vreg p .int) fl] := by
  rw [fresh_fst]
  have hfr := frag_one st (.loadAcquire (CTy.ofClif ty) (.vreg st.nextVreg .int) (.vreg p .int) fl)
    (by simp [vdefs, operands_loadAcquire, Operand.isDef])
  refine ⟨hfr.mono, hfr.defs, ?_⟩
  intro fr cm ρ w hf hv hdfg hmr
  show match Clif.evalInst fr cm (.atomicLoad ty fl p) with
    | .ok (vals, cm') => _ | .trap c => _ | .stuck _ => _
  cases he : Clif.evalInst fr cm (.atomicLoad ty fl p) with
  | trap c => intro h; simp [explicitTrapInst] at h
  | stuck _ => trivial
  | ok r =>
  obtain ⟨vals, cm'⟩ := r
  obtain ⟨pv, raw, hpv, hvalid, hread, rfl, rfl⟩ := evalInst_atomicLoad_inv hfl he
  dsimp only
  obtain ⟨ha, hA64, havoid⟩ := atom_addr hMRo hdfg hv hp64 hpv hmr hvalid
  rw [← ofClif_bytes hety] at havoid
  obtain ⟨w2, hs, hsw⟩ := hM.2.2.2.2.1 (CTy.ofClif ty) st.nextVreg p fl (ρ p) w
    (atomTy_ofClif hety) havoid
  have hr := seqRun_isem_one (operands_loadAcquire _ _ _ _) (ρ := ρ) hs rfl
  refine ⟨?_, _, w2, hr, .inr ⟨rfl, ?_⟩, hMR _ _ _ _ hsw.toNF hmr⟩
  · intro m hm u hu
    simp only [List.mem_singleton] at hm; subst hm
    have hu' : u = p := by simpa [vuseNums, operands_loadAcquire, Operand.isUse] using hu
    subst hu'
    exact .inr (by rw [hpv]; rfl)
  · intro j rs v hrs hv'
    cases j with
    | succ j => simp at hrs
    | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hrs hv'
    subst hrs hv'
    refine ⟨st.nextVreg, .int, rfl, .inl (Nat.le_refl _), ?_⟩
    have hbits := atom_read_eq hety hread hA64
      (fun i hi b hb => hMRo.bytes _ _ _ _ b hmr (valid_sub hvalid hi) hb)
    rw [← ha] at hbits
    have e : vdefUpd #[(⟨p, .int, .use, .early, .reg⟩ : Operand), ⟨st.nextVreg, .int, .def, .late, .reg⟩]
        [ofX ((Arm.read_mem_bytes (CTy.ofClif ty).bytes (lo64 (ρ p)) w).setWidth 64)] ρ st.nextVreg =
        ofX ((Arm.read_mem_bytes (CTy.ofClif ty).bytes (lo64 (ρ p)) w).setWidth 64) := by
      simp [vdefUpd, writeV, Operand.isDef, Operand.isEarly, Operand.isLate, upd]
    rw [e]
    exact atom_holds hety (ofClif_bytes_width hety) hbits

theorem atom_store_eq {ty : Clif.Ty} (hety : eTy ty = true) {cm : Clif.Mem} {A : Nat}
    {a : BitVec ty.width} {u : CV} (hh : VHolds ⟨ty, a⟩ u) :
    cm.writeBits false A ty.bytes a =
      cm.writeBits false A (CTy.ofClif ty).bytes ((lo64 u).setWidth ((CTy.ofClif ty).bytes * 8)) := by
  have hw := eTy_width hety
  have h8 : ty.bytes * 8 ≤ ty.width := by
    rw [← ofClif_bytes hety, ofClif_bytes_width hety]; exact Nat.le_refl _
  rw [writeBits_setWidth A ty.bytes a h8, store_setWidth hh h8 hw, ofClif_bytes hety]

/-- **`atomic_store`**: `stlr` of the value register at the address register. -/
theorem atomicStore_lower_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem)
    (hMRo : MemRelOk F sb syms f MR) {st : LState} {ty : Clif.Ty} {fl : Clif.MemFlags}
    {x p : Nat} {results : List Nat} (hety : eTy ty = true) (hfl : fl.endianness ≠ some .big)
    (hp64 : ctx.valueType? p = some (.int 64)) {t : CTy} (hvt : ctx.valueType? x = some t) :
    LowerInstOk isem MR env cp ctx (.atomicStore ty fl x p) results st []
      (st.emit (.storeRelease t (.vreg x .int) (.vreg p .int) fl))
      [.storeRelease t (.vreg x .int) (.vreg p .int) fl] := by
  have hfr := frag_emit0 st (.storeRelease t (.vreg x .int) (.vreg p .int) fl)
    (by simp [vdefs, operands_storeRelease, Operand.isDef])
  refine ⟨hfr.mono, hfr.defs, ?_⟩
  intro fr cm ρ w hf hv hdfg hmr
  show match Clif.evalInst fr cm (.atomicStore ty fl x p) with
    | .ok (vals, cm') => _ | .trap c => _ | .stuck _ => _
  cases he : Clif.evalInst fr cm (.atomicStore ty fl x p) with
  | trap c => intro h; simp [explicitTrapInst] at h
  | stuck _ => trivial
  | ok r =>
  obtain ⟨vals, cm'⟩ := r
  obtain ⟨a, pv, hax, hpv, hvalid, rfl, rfl⟩ := evalInst_atomicStore_inv hfl he
  have ht := hdfg.2 x t _ hvt (getAs_ok hax)
  subst ht
  dsimp only
  obtain ⟨ha, hA64, havoid⟩ := atom_addr hMRo hdfg hv hp64 hpv hmr hvalid
  rw [← ofClif_bytes hety] at havoid
  obtain ⟨w2, hs, hsw⟩ := hM.2.2.2.2.2.1 (CTy.ofClif ty) x p fl (ρ p) (ρ x) w
    (atomTy_ofClif hety) havoid
  have hr := seqRun_isem_one (operands_storeRelease _ _ _ _) (ρ := ρ) hs rfl
  have hxv := getAs_ok hax
  refine ⟨?_, _, w2, hr, .inr ⟨rfl, fun j rs v h => by simp at h⟩, ?_⟩
  · intro m hm u hu
    simp only [List.mem_singleton] at hm; subst hm
    have hu' : u = p ∨ u = x := by simpa [vuseNums, operands_storeRelease, Operand.isUse] using hu
    rcases hu' with rfl | rfl
    · exact .inr (by rw [hpv]; rfl)
    · exact .inr (by rw [hxv]; rfl)
  · refine hMR _ _ _ _ hsw.toNF ?_
    rw [atom_store_eq hety (hv x _ hxv), ha]
    exact hMRo.store _ _ _ _ _ _ hmr (by rw [ofClif_bytes hety]; exact hvalid)

theorem operands_rmwLoop (t : CTy) (op : AtomicRmwLoopOp) (fl : Clif.MemFlags) (p x d d1 d2 : Nat) :
    (MInst.atomicRmwLoop t op fl (.vreg p .int) (.vreg x .int) (.vreg d .int) (.vreg d1 .int)
      (.vreg d2 .int)).operands =
      .ok #[⟨p, .int, .use, .early, .fixed (.x 25)⟩, ⟨x, .int, .use, .early, .fixed (.x 26)⟩,
        ⟨d, .int, .def, .late, .fixed (.x 27)⟩, ⟨d1, .int, .def, .late, .fixed (.x 24)⟩,
        ⟨d2, .int, .def, .late, .fixed (.x 28)⟩] := rfl

theorem operands_casLoop (t : CTy) (fl : Clif.MemFlags) (p e x d d1 : Nat) :
    (MInst.atomicCasLoop t fl (.vreg p .int) (.vreg e .int) (.vreg x .int) (.vreg d .int)
      (.vreg d1 .int)).operands =
      .ok #[⟨p, .int, .use, .early, .fixed (.x 25)⟩, ⟨e, .int, .use, .early, .fixed (.x 26)⟩,
        ⟨x, .int, .use, .early, .fixed (.x 28)⟩, ⟨d, .int, .def, .late, .fixed (.x 27)⟩,
        ⟨d1, .int, .def, .late, .fixed (.x 24)⟩] := rfl

theorem frag_fresh3 (st : LState) (m : MInst)
    (hd : vdefs m = [st.nextVreg, st.nextVreg + 1, st.nextVreg + 2]) :
    Frag st ((((st.fresh .int).2.fresh .int).2.fresh .int).2.emit m) [m] := by
  refine ⟨by show st.emitted.push m = _; rw [Array.push_eq_append],
    by show st.nextVreg ≤ st.nextVreg + 1 + 1 + 1; omega, ?_⟩
  intro m' hm d hd'
  simp only [List.mem_singleton] at hm; subst hm
  rw [hd] at hd'
  show st.nextVreg ≤ d ∧ d < st.nextVreg + 1 + 1 + 1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'
  omega

theorem frag_fresh2 (st : LState) (m : MInst) (hd : vdefs m = [st.nextVreg, st.nextVreg + 1]) :
    Frag st (((st.fresh .int).2.fresh .int).2.emit m) [m] := by
  refine ⟨by show st.emitted.push m = _; rw [Array.push_eq_append],
    by show st.nextVreg ≤ st.nextVreg + 1 + 1; omega, ?_⟩
  intro m' hm d hd'
  simp only [List.mem_singleton] at hm; subst hm
  rw [hd] at hd'
  show st.nextVreg ≤ d ∧ d < st.nextVreg + 1 + 1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'
  omega

theorem writeBits_bits_congr {cm : Clif.Mem} {A n : Nat} {w1 w2 : Nat} (x : BitVec w1)
    (y : BitVec w2) (h : ∀ j < n * 8, x.getLsbD j = y.getLsbD j) :
    cm.writeBits false A n x = cm.writeBits false A n y := by
  simp only [Clif.Mem.writeBits]
  congr 1
  funext a
  split
  · rename_i ha
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    apply h
    simp only [Clif.Mem.byteIndex, Bool.false_eq_true, ite_false] at *
    omega
  · rfl

theorem bits_congr_atomicRmw {w1 w2 : Nat} (h : w1 = w2) (op : Clif.AtomicRmwOp)
    {a b : BitVec w1} {c d : BitVec w2} (hac : ∀ j, a.getLsbD j = c.getLsbD j)
    (hbd : ∀ j, b.getLsbD j = d.getLsbD j) :
    ∀ j, (Clif.Sem.atomicRmw op a b).getLsbD j = (Clif.Sem.atomicRmw op c d).getLsbD j := by
  subst h
  have e1 : a = c := BitVec.eq_of_getLsbD_eq fun j _ => hac j
  have e2 : b = d := BitVec.eq_of_getLsbD_eq fun j _ => hbd j
  subst e1 e2
  intro j; rfl

/-- The bits of a CLIF value held by a register, as its low bits at the access size. -/
theorem bits_setWidth_holds {ty : Clif.Ty} (hety : eTy ty = true) {a : BitVec ty.width} {u : CV}
    (hh : VHolds ⟨ty, a⟩ u) :
    ∀ j, a.getLsbD j = ((lo64 u).setWidth ((CTy.ofClif ty).bytes * 8)).getLsbD j := by
  intro j
  have hw := eTy_width hety
  have hb := ofClif_bytes_width hety
  simp only [VHolds] at hh
  rw [← hh]
  simp only [lo64, BitVec.getLsbD_setWidth, hb]
  by_cases hj : j < ty.width
  · simp [hj, show j < 64 by omega]
  · simp [hj]

/-- A value whose low bits at the access size are the loaded bytes holds the loaded CLIF value. -/
theorem holds_of_setWidth {ty : Clif.Ty} (hety : eTy ty = true) {raw : BitVec ty.width} {o : CV}
    {R : BitVec ((CTy.ofClif ty).bytes * 8)} (ho : o.setWidth ((CTy.ofClif ty).bytes * 8) = R)
    (hbits : ∀ j, raw.getLsbD j = R.getLsbD j) : VHolds ⟨ty, raw⟩ o := by
  simp only [VHolds]
  have hw := ofClif_bytes_width hety
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [hbits, ← ho]
  simp only [BitVec.getLsbD_setWidth]
  simp [hi, show i < (CTy.ofClif ty).bytes * 8 by omega]

/-- **`atomic_rmw`** with operation `cop` (`AtomicRMWLoop` with `op.clif = cop`): the old value
in the first fresh register, the new value in memory. -/
theorem atomicRmw_lower_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem)
    (hMRo : MemRelOk F sb syms f MR) {st : LState} {ty : Clif.Ty} {fl : Clif.MemFlags}
    {cop : Clif.AtomicRmwOp} {op : AtomicRmwLoopOp} (hop : op.clif = cop)
    {p x : Nat} {results : List Nat} (hety : eTy ty = true) (hfl : fl.endianness ≠ some .big)
    (hp64 : ctx.valueType? p = some (.int 64)) :
    LowerInstOk isem MR env cp ctx (.atomicRmw cop ty fl p x) results st [[(st.fresh .int).1]]
      ((((st.fresh .int).2.fresh .int).2.fresh .int).2.emit (.atomicRmwLoop (CTy.ofClif ty) op fl
        (.vreg p .int) (.vreg x .int) (st.fresh .int).1 ((st.fresh .int).2.fresh .int).1
        (((st.fresh .int).2.fresh .int).2.fresh .int).1))
      [.atomicRmwLoop (CTy.ofClif ty) op fl (.vreg p .int) (.vreg x .int) (st.fresh .int).1
        ((st.fresh .int).2.fresh .int).1 (((st.fresh .int).2.fresh .int).2.fresh .int).1] := by
  simp only [LState.fresh]
  have hfr := frag_fresh3 st (.atomicRmwLoop (CTy.ofClif ty) op fl (.vreg p .int) (.vreg x .int)
    (.vreg st.nextVreg .int) (.vreg (st.nextVreg + 1) .int) (.vreg (st.nextVreg + 2) .int))
    (by simp [vdefs, operands_rmwLoop, Operand.isDef])
  simp only [LState.fresh] at hfr
  refine ⟨hfr.mono, hfr.defs, ?_⟩
  intro fr cm ρ w hf hv hdfg hmr
  show match Clif.evalInst fr cm (.atomicRmw cop ty fl p x) with
    | .ok (vals, cm') => _ | .trap c => _ | .stuck _ => _
  cases he : Clif.evalInst fr cm (.atomicRmw cop ty fl p x) with
  | trap c => intro h; simp [explicitTrapInst] at h
  | stuck _ => trivial
  | ok r =>
  obtain ⟨vals, cm'⟩ := r
  obtain ⟨pv, a, old, hpv, hax, hvalid, hread, rfl, rfl⟩ := evalInst_atomicRmw_inv hfl he
  dsimp only
  obtain ⟨ha, hA64, havoid⟩ := atom_addr hMRo hdfg hv hp64 hpv hmr hvalid
  rw [← ofClif_bytes hety] at havoid
  obtain ⟨w2, o0, o1, o2, hs, ho0, hsw⟩ := hM.2.2.2.2.2.2.1 (CTy.ofClif ty) op fl p x st.nextVreg
    (st.nextVreg + 1) (st.nextVreg + 2) (ρ p) (ρ x) w (atomTy_ofClif hety) havoid
  have hr := seqRun_isem_one (operands_rmwLoop _ _ _ _ _ _ _ _) (ρ := ρ) hs rfl
  have hxv := getAs_ok hax
  have hbits := atom_read_eq hety hread hA64
    (fun i hi b hb => hMRo.bytes _ _ _ _ b hmr (valid_sub hvalid hi) hb)
  rw [← ha] at hbits
  refine ⟨?_, _, w2, hr, .inr ⟨rfl, ?_⟩, ?_⟩
  · intro m hm u hu
    simp only [List.mem_singleton] at hm; subst hm
    have hu' : u = p ∨ u = x := by simpa [vuseNums, operands_rmwLoop, Operand.isUse] using hu
    rcases hu' with rfl | rfl
    · exact .inr (by rw [hpv]; rfl)
    · exact .inr (by rw [hxv]; rfl)
  · intro j rs v hrs hv'
    cases j with
    | succ j => simp at hrs
    | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hrs hv'
    subst hrs hv'
    refine ⟨st.nextVreg, .int, rfl, .inl (Nat.le_refl _), ?_⟩
    have e : vdefUpd #[(⟨p, .int, .use, .early, .fixed (.x 25)⟩ : Operand),
        ⟨x, .int, .use, .early, .fixed (.x 26)⟩, ⟨st.nextVreg, .int, .def, .late, .fixed (.x 27)⟩,
        ⟨st.nextVreg + 1, .int, .def, .late, .fixed (.x 24)⟩,
        ⟨st.nextVreg + 2, .int, .def, .late, .fixed (.x 28)⟩]
        [o0, o1, o2] ρ st.nextVreg = o0 := by
      simp [vdefUpd, writeV, Operand.isDef, Operand.isEarly, Operand.isLate, upd]
    rw [e]
    exact holds_of_setWidth hety ho0 hbits
  · have hX := hv x _ hxv
    subst hop
    have hcm : cm.writeBits false (Clif.effAddr pv 0) ty.bytes (Clif.Sem.atomicRmw op.clif old a) =
        cm.writeBits false (Clif.effAddr pv 0) (CTy.ofClif ty).bytes
          (Clif.Sem.atomicRmw op.clif (Arm.read_mem_bytes (CTy.ofClif ty).bytes (lo64 (ρ p)) w)
            ((lo64 (ρ x)).setWidth ((CTy.ofClif ty).bytes * 8))) := by
      rw [← ofClif_bytes hety]
      exact writeBits_bits_congr _ _ fun j _ =>
        bits_congr_atomicRmw (ofClif_bytes_width hety).symm op.clif hbits
          (bits_setWidth_holds hety hX) j
    rw [hcm]
    refine hMR _ _ _ _ hsw ?_
    rw [ha]
    exact hMRo.store _ _ _ _ _ _ hmr (by rw [ofClif_bytes hety]; exact hvalid)


/-- Equal values from equal bits (at equal widths). -/
theorem bits_eq_iff {w1 w2 : Nat} (h : w1 = w2) {a b : BitVec w1} {c d : BitVec w2}
    (hac : ∀ j, a.getLsbD j = c.getLsbD j) (hbd : ∀ j, b.getLsbD j = d.getLsbD j) :
    a = b ↔ c = d := by
  subst h
  have e1 : a = c := BitVec.eq_of_getLsbD_eq fun j _ => hac j
  have e2 : b = d := BitVec.eq_of_getLsbD_eq fun j _ => hbd j
  rw [e1, e2]

/-- **`atomic_cas`**: the old value in the first fresh register; the replacement value in
memory if the old value is the expected one. -/
theorem atomicCas_lower_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem)
    (hMRo : MemRelOk F sb syms f MR) {st : LState} {ty : Clif.Ty} {fl : Clif.MemFlags}
    {p e x : Nat} {results : List Nat} (hety : eTy ty = true) (hfl : fl.endianness ≠ some .big)
    (hp64 : ctx.valueType? p = some (.int 64)) :
    LowerInstOk isem MR env cp ctx (.atomicCas ty fl p e x) results st [[(st.fresh .int).1]]
      (((st.fresh .int).2.fresh .int).2.emit (.atomicCasLoop (CTy.ofClif ty) fl
        (.vreg p .int) (.vreg e .int) (.vreg x .int) (st.fresh .int).1
        ((st.fresh .int).2.fresh .int).1))
      [.atomicCasLoop (CTy.ofClif ty) fl (.vreg p .int) (.vreg e .int) (.vreg x .int)
        (st.fresh .int).1 ((st.fresh .int).2.fresh .int).1] := by
  simp only [LState.fresh]
  have hfr := frag_fresh2 st (.atomicCasLoop (CTy.ofClif ty) fl (.vreg p .int) (.vreg e .int)
    (.vreg x .int) (.vreg st.nextVreg .int) (.vreg (st.nextVreg + 1) .int))
    (by simp [vdefs, operands_casLoop, Operand.isDef])
  simp only [LState.fresh] at hfr
  refine ⟨hfr.mono, hfr.defs, ?_⟩
  intro fr cm ρ w hf hv hdfg hmr
  show match Clif.evalInst fr cm (.atomicCas ty fl p e x) with
    | .ok (vals, cm') => _ | .trap c => _ | .stuck _ => _
  cases he : Clif.evalInst fr cm (.atomicCas ty fl p e x) with
  | trap c => intro h; simp [explicitTrapInst] at h
  | stuck _ => trivial
  | ok r =>
  obtain ⟨vals, cm'⟩ := r
  obtain ⟨pv, ev, a, old, hpv, hev, hax, hvalid, hread, rfl, rfl⟩ := evalInst_atomicCas_inv hfl he
  dsimp only
  obtain ⟨ha, hA64, havoid⟩ := atom_addr hMRo hdfg hv hp64 hpv hmr hvalid
  rw [← ofClif_bytes hety] at havoid
  obtain ⟨w2, o1, hs, hsw⟩ := hM.2.2.2.2.2.2.2.1 (CTy.ofClif ty) fl p e x st.nextVreg
    (st.nextVreg + 1) (ρ p) (ρ e) (ρ x) w (atomTy_ofClif hety) havoid
  have hr := seqRun_isem_one (operands_casLoop _ _ _ _ _ _ _) (ρ := ρ) hs rfl
  have hev' := getAs_ok hev
  have hxv := getAs_ok hax
  have hbits := atom_read_eq hety hread hA64
    (fun i hi b hb => hMRo.bytes _ _ _ _ b hmr (valid_sub hvalid hi) hb)
  rw [← ha] at hbits
  refine ⟨?_, _, w2, hr, .inr ⟨rfl, ?_⟩, ?_⟩
  · intro m hm u hu
    simp only [List.mem_singleton] at hm; subst hm
    have hu' : u = p ∨ u = e ∨ u = x := by
      simpa [vuseNums, operands_casLoop, Operand.isUse] using hu
    rcases hu' with rfl | rfl | rfl
    · exact .inr (by rw [hpv]; rfl)
    · exact .inr (by rw [hev']; rfl)
    · exact .inr (by rw [hxv]; rfl)
  · intro j rs v hrs hv'
    cases j with
    | succ j => simp at hrs
    | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hrs hv'
    subst hrs hv'
    refine ⟨st.nextVreg, .int, rfl, .inl (Nat.le_refl _), ?_⟩
    have e : vdefUpd #[(⟨p, .int, .use, .early, .fixed (.x 25)⟩ : Operand),
        ⟨e, .int, .use, .early, .fixed (.x 26)⟩, ⟨x, .int, .use, .early, .fixed (.x 28)⟩,
        ⟨st.nextVreg, .int, .def, .late, .fixed (.x 27)⟩,
        ⟨st.nextVreg + 1, .int, .def, .late, .fixed (.x 24)⟩]
        [ofX ((Arm.read_mem_bytes (CTy.ofClif ty).bytes (lo64 (ρ p)) w).setWidth 64), o1] ρ
        st.nextVreg = ofX ((Arm.read_mem_bytes (CTy.ofClif ty).bytes (lo64 (ρ p)) w).setWidth 64) := by
      simp [vdefUpd, writeV, Operand.isDef, Operand.isEarly, Operand.isLate, upd]
    rw [e]
    exact atom_holds hety (ofClif_bytes_width hety) hbits
  · have hE := bits_setWidth_holds hety (hv e _ hev')
    have hiff := bits_eq_iff (ofClif_bytes_width hety).symm hbits hE
    refine hMR _ _ _ _ hsw ?_
    by_cases hc : old = ev
    · rw [if_pos hc, if_pos (hiff.1 hc), atom_store_eq hety (hv x _ hxv), ha]
      exact hMRo.store _ _ _ _ _ _ hmr (by rw [ofClif_bytes hety]; exact hvalid)
    · rw [if_neg hc, if_neg (fun h => hc (hiff.2 h))]
      exact hmr

end Builders

/-! ## `bmask` (`lower.isle:2052`, rule id 936) -/

theorem instNames_bmask {c : Clif.Inst} (h : instNames c = ("Unary", "Bmask")) :
    ∃ ty x, c = .bmask ty x := by
  cases c <;> simp only [instNames, Prod.mk.injEq] at h
  all_goals first
    | exact ⟨_, _, rfl⟩
    | (exfalso; simp at h; done)
    | (exfalso; rename_i op _ _; cases op <;> simp [unaryOpcode] at h; done)
    | (exfalso; rename_i op _ _; cases op <;> simp at h; done)

theorem instData_bmask {f : Clif.Function} {ty : Clif.Ty} {x ko : Nat} {fs : List V}
    (h : instData f (.bmask ty x) = .ok (.data 152 29 (.data 151 ko [] :: fs))) :
    eTy ty = true ∧ fs = [.value x] := by
  simp only [instData] at h
  split at h
  · rename_i he
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
    injection h3 with _ h4
    exact ⟨he, h4⟩
  · cases h

theorem evalInst_bmask_ok {fr : Clif.Frame} {cm cm' : Clif.Mem} {ty : Clif.Ty} {x : Nat}
    {vals : List Clif.Val} (h : Clif.evalInst fr cm (.bmask ty x) = .ok (vals, cm')) :
    ∃ a, fr.regs x = some a ∧ vals = [⟨ty, Clif.Sem.bmask a.bits⟩] ∧ cm' = cm := by
  simp only [Clif.evalInst, Clif.Frame.get] at h
  cases hx : fr.regs x with
  | none => rw [hx] at h; cases h
  | some a =>
    rw [hx] at h
    simp [Clif.Res.ofOption, bind, Clif.Res.bind, pure] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨a, rfl, rfl, rfl⟩

/-- `a ↔ b` on bit-vector propositions, by `bv_decide` both ways. -/
macro "decide_bv_iff" : tactic => `(tactic| (constructor <;> intro h <;> bv_decide))

section BmaskRun
variable {F : BitVec 64 → Prop} {isem : Sem}

theorem ispec_csetm_ne (d : Nat) (w : Arm.ArmState) :
    ispec (.csetm (.vreg d .int) .ne) [] w = some ([ofX (if Arm.ConditionHolds Cond.ne.invert.bits w
      then 0#64 else BitVec.allOnes 64)], w, .next) := by
  simp [ispec, defOut]

theorem ispec_and_imm32 (t x : Nat) (m : Nat) (hm : ImmLogic.ofNat? m .size32 = some ⟨m, .size32⟩)
    (a : CV) (w : Arm.ArmState) :
    ispec (.aluRRImmLogic .and .size32 (.vreg t .int) (.vreg x .int) ⟨m, .size32⟩) [a] w =
      some ([resX .size32 (opnd .size32 a &&& BitVec.ofNat OperandSize.size32.bits m)], w, .next) := by
  simp [ispec, hm, aluVal, defOut]

/-- `cmp x, #0; csetm d, ne`: `d` is all ones if the low `sz` bits of `x` are non-zero. -/
theorem runs_bmask (hR : Refines F isem) (sz : OperandSize) (x d : Nat) (ρ : Nat → CV)
    (w : Arm.ArmState) :
    Runs F isem [.aluRRImm12 .subS sz .xzr (.vreg x .int) ⟨0, false⟩, .csetm (.vreg d .int) .ne]
      ρ w (fun ρ' _ => ρ' d = ofX (if opnd sz (ρ x) = 0 then 0#64 else BitVec.allOnes 64)) := by
  refine Runs.append (ms1 := [_]) (Runs.flags hR (setsFlags_cmp_imm0 sz x ρ) w)
    fun ρ1 w1 ⟨h1, h2⟩ => ?_
  subst h1
  refine (Runs.one hR rfl (ispec_csetm_ne d w1) rfl (SameWorldNF.refl F w1)
    (P := fun ρ' _ => ρ' d = ofX (if Arm.ConditionHolds Cond.ne.invert.bits w1 then 0#64
      else BitVec.allOnes 64)) fun _ _ => by
        simp [vdefUpd, writeV, Operand.isDef, Operand.isEarly, Operand.isLate, OpSpec.def_, upd]).imp ?_
  intro ρ' _ _ h
  rw [h, h2, condOn_invert _ (by decide), (condOn_cmp_zero sz _).1]
  simp

/-- `and t, x, #m; cmp t, #0; csetm d, ne` (32-bit): `d` is all ones if `x & m` is non-zero. -/
theorem runs_bmask_masked (hR : Refines F isem) (m : Nat)
    (hm : ImmLogic.ofNat? m .size32 = some ⟨m, .size32⟩) (x t d : Nat) (ρ : Nat → CV)
    (w : Arm.ArmState) :
    Runs F isem [.aluRRImmLogic .and .size32 (.vreg t .int) (.vreg x .int) ⟨m, .size32⟩,
        .aluRRImm12 .subS .size32 .xzr (.vreg t .int) ⟨0, false⟩, .csetm (.vreg d .int) .ne]
      ρ w (fun ρ' _ => ρ' d = ofX (if opnd .size32 (ρ x) &&& BitVec.ofNat OperandSize.size32.bits m = 0 then 0#64
        else BitVec.allOnes 64)) := by
  refine Runs.append (ms1 := [_]) (Runs.one hR rfl (ispec_and_imm32 t x m hm (ρ x) w) rfl
    (SameWorldNF.refl F w) (P := fun ρ' _ => ρ' = upd ρ t (resX .size32 (opnd .size32 (ρ x) &&&
      BitVec.ofNat OperandSize.size32.bits m))) fun _ _ => by
        simp [vdefUpd, writeV, Operand.isDef, Operand.isEarly, Operand.isLate, OpSpec.def_, upd])
    fun ρ1 w1 h1 => ?_
  subst h1
  refine (runs_bmask hR .size32 t d _ w1).imp fun ρ' _ _ h => ?_
  rw [h]
  simp only [upd, ↓reduceIte, opnd_resX]

/-! ### The value: `bmask` of the operand -/

theorem vholds_bmask {ty : Clif.Ty} (hety : eTy ty = true) {v : Nat} (b : BitVec v) :
    VHolds ⟨ty, Clif.Sem.bmask b⟩
      (ofX (if Clif.Sem.truthy b = false then 0#64 else BitVec.allOnes 64)) := by
  have hw := eTy_width hety
  unfold Clif.Sem.bmask
  split
  · rename_i h
    simp only [h, Bool.true_eq_false, ↓reduceIte, VHolds]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [ofX, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
    simp [hi, show i < 128 by omega, show i < 64 by omega]
  · rename_i h
    simp only [Bool.not_eq_true] at h
    simp only [h, ↓reduceIte, VHolds]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [ofX, BitVec.getLsbD_setWidth]

theorem opnd_eq_setWidth (sz : OperandSize) (u : CV) : opnd sz u = u.setWidth sz.bits := by
  simp only [opnd, lo64, BitVec.setWidth_setWidth_of_le _ (opSize_bits_le sz)]

theorem and_mask8 (u : BitVec 128) : u.setWidth 32 &&& 255#32 = 0 ↔ u.setWidth 8 = 0 := by
  constructor <;> intro h <;> bv_decide

theorem and_mask16 (u : BitVec 128) : u.setWidth 32 &&& 65535#32 = 0 ↔ u.setWidth 16 = 0 := by
  constructor <;> intro h <;> bv_decide

theorem bmask_cond_3264 {wi : Nat} (hwi : wi = 32 ∨ wi = 64) {a : Clif.Val}
    (hty : CTy.ofClif a.ty = .int wi) {u : CV} (hh : VHolds a u) :
    opnd (szOf wi) u = 0 ↔ Clif.Sem.truthy a.bits = false := by
  rw [opnd_eq_setWidth]
  obtain ⟨aty, ab⟩ := a
  rcases hwi with rfl | rfl <;> cases aty <;> simp [CTy.ofClif] at hty <;>
    simp only [VHolds] at hh <;> subst hh <;> simp [Clif.Sem.truthy, szOf, OperandSize.bits] <;> rfl

theorem bmask_cond_816 {wi : Nat} (hwi : wi = 8 ∨ wi = 16) {a : Clif.Val}
    (hty : CTy.ofClif a.ty = .int wi) {u : CV} (hh : VHolds a u) :
    opnd .size32 u &&& BitVec.ofNat OperandSize.size32.bits (2 ^ wi - 1) = 0 ↔
      Clif.Sem.truthy a.bits = false := by
  rw [opnd_eq_setWidth]
  obtain ⟨aty, ab⟩ := a
  rcases hwi with rfl | rfl <;> cases aty <;> simp [CTy.ofClif] at hty <;>
    simp only [VHolds] at hh <;> subst hh <;> simp only [Clif.Sem.truthy, bne_eq_false_iff_eq]
  · exact and_mask8 u
  · exact and_mask16 u

end BmaskRun

/-! ### `LowerInstOk` of the two code shapes -/

theorem vdefs_cmpImm0' (sz : OperandSize) (x : Nat) (i : Imm12) :
    vdefs (.aluRRImm12 .subS sz .xzr (.vreg x .int) i) = [] := rfl
theorem vuseNums_cmpImm0' (sz : OperandSize) (x : Nat) (i : Imm12) :
    vuseNums (.aluRRImm12 .subS sz .xzr (.vreg x .int) i) = [x] := rfl
theorem vdefs_csetm (d : Nat) (c : Cond) : vdefs (.csetm (.vreg d .int) c) = [d] := rfl
theorem vuseNums_csetm (d : Nat) (c : Cond) : vuseNums (.csetm (.vreg d .int) c) = [] := rfl

section BmaskLower
variable {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
  {ctx : Ctx}

theorem bmask_lower_3264 (hR : Refines F isem) (hMR : MRStable F MR) {st : LState} {ty : Clif.Ty}
    {x wi : Nat} {results : List Nat} (hety : eTy ty = true) (hwi : wi = 32 ∨ wi = 64)
    (hvt : ctx.valueType? x = some (.int wi)) :
    LowerInstOk isem MR env cp ctx (.bmask ty x) results st [[(st.fresh .int).1]]
      (((st.fresh .int).2.emit (.aluRRImm12 .subS (szOf wi) .xzr (.vreg x .int) ⟨0, false⟩)).emit
        (.csetm (st.fresh .int).1 .ne))
      [.aluRRImm12 .subS (szOf wi) .xzr (.vreg x .int) ⟨0, false⟩, .csetm (st.fresh .int).1 .ne] := by
  rw [fresh_fst]
  refine lowerInstOk_runs (d := st.nextVreg) hMR (by simp [LState.emit, LState.fresh]) ?_ rfl ?_
  · intro m hm d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · simp [vdefs_cmpImm0'] at hd
    · simp [vdefs_csetm] at hd
      subst hd
      simp [LState.emit, LState.fresh]
  · intro fr cm ρ w vals cm' _ hv hdfg ho
    obtain ⟨a, ha, rfl, rfl⟩ := evalInst_bmask_ok ho
    have hty := hdfg.2 x _ a hvt ha
    refine ⟨rfl, usesOk_of [x] ?_ ?_, .inl (Nat.le_refl _), _, rfl,
      (runs_bmask hR (szOf wi) x st.nextVreg ρ w).imp fun ρ' _ _ h => ?_⟩
    · intro m hm u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl <;> simp [vuseNums_cmpImm0', vuseNums_csetm] at hu <;> simp [hu]
    · intro y hy
      simp only [List.mem_singleton] at hy
      subst hy
      simp [ha]
    · rw [h]
      have hc := bmask_cond_3264 hwi hty (hv x a ha)
      have := vholds_bmask hety a.bits
      by_cases hz : opnd (szOf wi) (ρ x) = 0
      · simp only [hc.mp hz, ↓reduceIte] at this
        simpa only [hz, ↓reduceIte] using this
      · have hf : Clif.Sem.truthy a.bits = true := by
          cases h' : Clif.Sem.truthy a.bits
          · exact absurd (hc.mpr h') hz
          · rfl
        simp only [hf, Bool.true_eq_false, ↓reduceIte] at this
        simpa only [hz, ↓reduceIte] using this

theorem bmask_lower_816 (hR : Refines F isem) (hMR : MRStable F MR) {st : LState} {ty : Clif.Ty}
    {x wi : Nat} {results : List Nat} (hety : eTy ty = true) (hwi : wi = 8 ∨ wi = 16)
    (hvt : ctx.valueType? x = some (.int wi)) :
    LowerInstOk isem MR env cp ctx (.bmask ty x) results st
      [[(((st.fresh .int).2.emit (.aluRRImmLogic .and .size32 (st.fresh .int).1 (.vreg x .int)
        ⟨2 ^ wi - 1, .size32⟩)).fresh .int).1]]
      (((((st.fresh .int).2.emit (.aluRRImmLogic .and .size32 (st.fresh .int).1 (.vreg x .int)
        ⟨2 ^ wi - 1, .size32⟩)).fresh .int).2.emit
          (.aluRRImm12 .subS .size32 .xzr (st.fresh .int).1 ⟨0, false⟩)).emit
        (.csetm (((st.fresh .int).2.emit (.aluRRImmLogic .and .size32 (st.fresh .int).1
          (.vreg x .int) ⟨2 ^ wi - 1, .size32⟩)).fresh .int).1 .ne))
      [.aluRRImmLogic .and .size32 (st.fresh .int).1 (.vreg x .int) ⟨2 ^ wi - 1, .size32⟩,
        .aluRRImm12 .subS .size32 .xzr (st.fresh .int).1 ⟨0, false⟩,
        .csetm (((st.fresh .int).2.emit (.aluRRImmLogic .and .size32 (st.fresh .int).1
          (.vreg x .int) ⟨2 ^ wi - 1, .size32⟩)).fresh .int).1 .ne] := by
  have e1 : (((st.fresh .int).2.emit (.aluRRImmLogic .and .size32 (st.fresh .int).1 (.vreg x .int)
      ⟨2 ^ wi - 1, .size32⟩)).fresh .int).1 = .vreg (st.nextVreg + 1) .int := by
    simp [LState.fresh, LState.emit]
  rw [e1, fresh_fst]
  have hm : ImmLogic.ofNat? (2 ^ wi - 1) .size32 = some ⟨2 ^ wi - 1, .size32⟩ := by
    rcases hwi with rfl | rfl <;> rfl
  refine lowerInstOk_runs (d := st.nextVreg + 1) hMR (by simp [LState.emit, LState.fresh]; omega)
    ?_ rfl ?_
  · intro m hm d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;>
      simp [vdd_aluRRImmLogic, vdefs_cmpImm0', vdefs_csetm] at hd <;> subst hd <;>
      simp [LState.emit, LState.fresh] <;> omega
  · intro fr cm ρ w vals cm' _ hv hdfg ho
    obtain ⟨a, ha, rfl, rfl⟩ := evalInst_bmask_ok ho
    have hty := hdfg.2 x _ a hvt ha
    refine ⟨rfl, usesOk_of [x] ?_ ?_, .inl (by omega), _, rfl,
      (runs_bmask_masked hR _ hm x st.nextVreg (st.nextVreg + 1) ρ w).imp fun ρ' _ _ h => ?_⟩
    · intro m hm u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl <;>
        simp [vdu_aluRRImmLogic, vuseNums_cmpImm0', vuseNums_csetm] at hu <;> simp [hu]
    · intro y hy
      simp only [List.mem_singleton] at hy
      subst hy
      simp [ha]
    · rw [h]
      have hc := bmask_cond_816 hwi hty (hv x a ha)
      have := vholds_bmask hety a.bits
      by_cases hz : opnd .size32 (ρ x) &&& BitVec.ofNat OperandSize.size32.bits (2 ^ wi - 1) = 0
      · simp only [hc.mp hz, ↓reduceIte] at this
        simpa only [hz, ↓reduceIte] using this
      · have hf : Clif.Sem.truthy a.bits = true := by
          cases h' : Clif.Sem.truthy a.bits
          · exact absurd (hc.mpr h') hz
          · rfl
        simp only [hf, Bool.true_eq_false, ↓reduceIte] at this
        simpa only [hz, ↓reduceIte] using this

end BmaskLower

section Bmask
variable {p : Program} (hp : Data p)

set_option maxHeartbeats 4000000 in
include hp in
/-- **`bmask`** (`lower.isle:2052`): `cmp #0` (an 8/16-bit value masked first), `csetm ne`. -/
theorem bmask_ok (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_2052 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  mem_inv hp [ctor_put_in_regs_iff] at hmatch heval
  have hdat0 := hctx.data _ _ _ hi hic
  have hRT := hctx.resTys _ _ _ hi hic
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hdat := data_trans hdat0 ‹_›
  obtain ⟨hf, ho⟩ := instData_inv_names hdat
  rw [atom_vn_Unary] at hf
  rw [atom_vn_Bmask] at ho
  obtain ⟨ty, x, rfl⟩ :=
    instNames_bmask (Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm)
  obtain ⟨hety, hfs⟩ := instData_bmask hdat
  simp only [List.cons.injEq, and_true] at hfs
  subst hfs
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at *
  isel_destruct; subst_vars
  repeat (mem_inv_simp [ctor_put_in_regs_iff] at * <;> isel_destruct <;> subst_vars)
  simp only [‹_ = List.map CTy.ofClif [ty]›, List.map_cons, List.map_nil, List.head?_cons,
    Option.getD_some, ofClif_int_width] at *
  have := hctx.valueReg x _ ‹ctx.valueReg? x = some _›; subst this
  have hvt := ‹ctx.valueType? x = some _›
  have hE := hctx.valTyE x _ hvt
  simp only [eCTys, List.mem_cons, List.not_mem_nil, or_false] at hE
  have hw := eTy_width hety
  have hcall := ‹ApplyInternal _ _ _ _ 22 658 _ _ _ _›
  have hout := ‹externCtor ctx T.output _ _ = _›
  rcases hE with rfl | rfl | rfl | rfl
  · obtain ⟨rfl, hs⟩ := lower_bmask_816_ok hp hco (by omega) hw (.inl rfl) hcall
    rw [ctor_output'] at hout
    obtain ⟨rfl, rfl⟩ := hout
    rw [hs]
    exact ⟨_, by simp [LState.emit, LState.fresh, arr_push3], _, rfl,
      bmask_lower_816 hR hMR hety (.inl rfl) hvt⟩
  · obtain ⟨rfl, hs⟩ := lower_bmask_816_ok hp hco (by omega) hw (.inr rfl) hcall
    rw [ctor_output'] at hout
    obtain ⟨rfl, rfl⟩ := hout
    rw [hs]
    exact ⟨_, by simp [LState.emit, LState.fresh, arr_push3], _, rfl,
      bmask_lower_816 hR hMR hety (.inr rfl) hvt⟩
  · obtain ⟨rfl, hs⟩ := lower_bmask_3264_ok hp hco (by omega) hw (.inl rfl) hcall
    rw [ctor_output'] at hout
    obtain ⟨rfl, rfl⟩ := hout
    rw [hs]
    exact ⟨_, by simp [LState.emit, LState.fresh, arr_push2], _, rfl,
      bmask_lower_3264 hR hMR hety (.inl rfl) hvt⟩
  · obtain ⟨rfl, hs⟩ := lower_bmask_3264_ok hp hco (by omega) hw (.inr rfl) hcall
    rw [ctor_output'] at hout
    obtain ⟨rfl, rfl⟩ := hout
    rw [hs]
    exact ⟨_, by simp [LState.emit, LState.fresh, arr_push2], _, rfl,
      bmask_lower_3264 hR hMR hety (.inr rfl) hvt⟩

end Bmask

/-! ## `fence` (`lower.isle:2476`, rule id 1024) -/

theorem instNames_fence {c : Clif.Inst} (h : instNames c = ("NullAry", "Fence")) : c = .fence := by
  cases c <;> simp [instNames] at h ⊢
  all_goals first
    | (rename_i op _ _; cases op <;> simp [unaryOpcode] at h)
    | (rename_i op _ _ _; cases op <;> simp [binaryOpcode] at h)
    | (rename_i op _ _ _; cases op <;> simp [divOpcode] at h)
    | (rename_i op _ _; cases op <;> simp at h)
    | (rename_i op _ _ _ _ _; cases op <;> simp [loadOpcode] at h)
    | (rename_i op _ _ _ _ _ _; cases op <;> simp [storeOpcode] at h)
    | skip

section Fence
variable {p : Program} (hp : Data p)

set_option maxHeartbeats 2000000 in
include hp in
/-- **`fence`** (`lower.isle:2476`): `dmb ish`, no effect in the single-threaded model. -/
theorem fence_ok (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_2476 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  obtain ⟨tys, htys, -, hlen⟩ := hctx.resTys _ _ _ hi hic
  mem_inv hp [] at hmatch heval
  have hdat0 := hctx.data _ _ _ hi hic
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hdat := data_trans hdat0 ‹_›
  obtain ⟨hf, ho⟩ := instData_inv_names hdat
  rw [atom_vn_NullAry] at hf
  rw [atom_vn_Fence] at ho
  have := instNames_fence (Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm)
  subst this
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hF := ‹ApplyInternal _ _ _ _ 46 466 _ _ _ _›
  have hSE := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  obtain ⟨rfl, hs4⟩ := fence_helper_ok hp hco (by omega) hF
  obtain ⟨mi, hmi, hs', rfl⟩ := side_effect_inst_ok hp hco (ctx := ctx) (by omega) hSE
  have hmi' : MInst.ofV (.data 58 44 []) = some .fence := rfl
  rw [hmi', Option.some.injEq] at hmi
  subst hmi
  simp only at hs' hs4
  rw [hs4] at hs'
  subst hs'
  have hres := List.eq_nil_of_length_eq_zero hlen
  have hfr := frag_emit0 st .fence rfl
  refine ⟨[.fence], hfr.emitted, [], rfl, ⟨hfr.mono, hfr.defs, ?_⟩⟩
  intro fr cm ρ w _ _ _ hmr
  have ho : instOutcome env cp fr cm .fence = .ok ([], cm) := rfl
  rw [ho]
  obtain ⟨w'', hs, hsw⟩ := hR .fence [] w [] w (ctl := .next) rfl
  refine ⟨fun m hm u hu => ?_, _, w'', seqRun_isem_one (ops := #[]) rfl hs rfl, .inl hres,
    hMR _ _ _ _ hsw.toNF hmr⟩
  simp only [List.mem_singleton] at hm
  subst hm
  simp [show vuseNums MInst.fence = [] from rfl] at hu

end Fence

/-! ## The root rules -/

theorem ext_valid_atomic_transaction_iff (ctx : Ctx) (st : LState) (ty : CTy) (fs : List V) :
    externExtract ctx T.valid_atomic_transaction (.ty ty) st = .ok fs ↔
      (ty == .int 8 || ty == .int 16 || ty == .int 32 || ty == .int 64) = true ∧
        fs = [.ty ty] := by
  have : externExtract ctx T.valid_atomic_transaction (.ty ty) st =
    if (ty == .int 8 || ty == .int 16 || ty == .int 32 || ty == .int 64) = true then
      .ok [.ty ty] else .fail := rfl
  rw [this]; clear this
  split
  · rename_i h; simp only [h, ExtResult.ok.injEq, true_and]; exact eq_comm
  · rename_i h; simp only [h, reduceCtorEq, false_iff, not_and, Bool.false_eq_true]
    intro h'; exact h'.elim

theorem ofV_loadAcquire (t : CTy) (rd rn : Reg) (fl : Clif.MemFlags) :
    MInst.ofV (.data 58 42 [.ty t, .reg rd, .reg rn, .op (.memFlags fl)]) =
      some (.loadAcquire t rd rn fl) := rfl

theorem ofV_storeRelease (t : CTy) (rt rn : Reg) (fl : Clif.MemFlags) :
    MInst.ofV (.data 58 43 [.ty t, .reg rt, .reg rn, .op (.memFlags fl)]) =
      some (.storeRelease t rt rn fl) := rfl

theorem inv_atomicStore_root {f : Clif.Function} {cl : Clif.Inst} {w1 w2 : V}
    (h : instData f cl = .ok (.data 152 23 [.data 151 159 [], w1, w2])) :
    ∃ ty fl x p, cl = .atomicStore ty fl x p ∧ w1 = .values [x, p] ∧
      w2 = .op (.memFlags fl) ∧ eTy ty = true ∧ fl.endianness ≠ some .big := by
  have hn := instData_names_eq h atom_vn_StoreNoOffset atom_vn_AtomicStore
  cases cl <;> simp only [instNames, Prod.mk.injEq] at hn
  all_goals try (simp at hn; done)
  rename_i ty fl x p
  simp only [instData] at h
  split at h
  · cases h
  · rename_i he
    split at h
    · cases h
    · rename_i hb
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
      simp only [List.cons.injEq, and_true] at h3
      obtain ⟨-, rfl, rfl⟩ := h3
      exact ⟨ty, fl, x, p, rfl, rfl, rfl, by simpa using he, by simpa using hb⟩

theorem inv_atomicLoad_root {f : Clif.Function} {cl : Clif.Inst} {w1 w2 : V}
    (h : instData f cl = .ok (.data 152 17 [.data 151 158 [], w1, w2])) :
    ∃ ty fl p, cl = .atomicLoad ty fl p ∧ w1 = .value p ∧ w2 = .op (.memFlags fl) ∧
      eTy ty = true ∧ fl.endianness ≠ some .big := by
  have hn := instData_names_eq h atom_vn_LoadNoOffset atom_vn_AtomicLoad
  cases cl <;> simp only [instNames, Prod.mk.injEq] at hn
  all_goals try (simp at hn; done)
  rename_i ty fl p
  simp only [instData] at h
  split at h
  · cases h
  · rename_i he
    split at h
    · cases h
    · rename_i hb
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
      simp only [List.cons.injEq, and_true] at h3
      obtain ⟨-, rfl, rfl⟩ := h3
      exact ⟨ty, fl, p, rfl, rfl, rfl, by simpa using he, by simpa using hb⟩

theorem inv_atomicRmw_root {f : Clif.Function} {cl : Clif.Inst} {w1 w2 : V} {k : Nat}
    (h : instData f cl = .ok (.data 152 1 [.data 151 156 [], w1, w2, .data 143 k []])) :
    ∃ op ty fl p x nm, cl = .atomicRmw op ty fl p x ∧ w1 = .values [p, x] ∧
      w2 = .op (.memFlags fl) ∧ rmwOpName op = some nm ∧ (variantNames 143)[k]? = some nm ∧
      eTy ty = true ∧ fl.endianness ≠ some .big := by
  have hn := instData_names_eq h atom_vn_AtomicRmwF atom_vn_AtomicRmw
  cases cl <;> simp only [instNames, Prod.mk.injEq] at hn
  all_goals try (simp at hn; done)
  all_goals try (rename_i op _ _; cases op <;> simp at hn; done)
  all_goals try (rename_i op _ _ _; cases op <;> simp at hn; done)
  rename_i op ty fl p x
  simp only [instData] at h
  split at h
  · cases h
  · rename_i he
    split at h
    · cases h
    · rename_i hb
      split at h
      · rename_i nm hnm
        simp only [pure, Except.pure, Except.ok.injEq] at h
        obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
        simp only [List.cons.injEq, and_true] at h3
        obtain ⟨-, rfl, rfl, h4⟩ := h3
        obtain ⟨hk, -, -⟩ := mkVariant_eq_data h4.symm
        exact ⟨op, ty, fl, p, x, nm, rfl, rfl, rfl, hnm, hk, by simpa using he, by simpa using hb⟩
      · cases h

theorem inv_atomicCas_root {f : Clif.Function} {cl : Clif.Inst} {w1 w2 : V}
    (h : instData f cl = .ok (.data 152 0 [.data 151 157 [], w1, w2])) :
    ∃ ty fl p e x, cl = .atomicCas ty fl p e x ∧ w1 = .values [p, e, x] ∧
      w2 = .op (.memFlags fl) ∧ eTy ty = true ∧ fl.endianness ≠ some .big := by
  have hn := instData_names_eq h atom_vn_AtomicCasF atom_vn_AtomicCas
  cases cl <;> simp only [instNames, Prod.mk.injEq] at hn
  all_goals try (simp at hn; done)
  all_goals try (rename_i op _ _; cases op <;> simp at hn; done)
  all_goals try (rename_i op _ _ _; cases op <;> simp at hn; done)
  rename_i ty fl p e x
  simp only [instData] at h
  split at h
  · cases h
  · rename_i he
    split at h
    · cases h
    · rename_i hb
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
      simp only [List.cons.injEq, and_true] at h3
      obtain ⟨-, rfl, rfl⟩ := h3
      exact ⟨ty, fl, p, e, x, rfl, rfl, rfl, by simpa using he, by simpa using hb⟩

section Roots
variable {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {sb : Nat}
  {syms : String → Option Nat} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}

set_option maxHeartbeats 2000000 in
include hp in
/-- **`atomic_load`** (`lower.isle:2316`, rule id 983): `ldar`. -/
theorem atomic_load_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2316 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [ext_valid_atomic_transaction_iff] at hmatch heval
  have hdat0 := hctx.data _ _ _ hi hic
  have hA64 := fun x => hctx.addr64 _ _ _ x hi hic
  have hRT := hctx.resTys _ _ _ hi hic
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hdat := data_trans hdat0 ‹_›
  obtain ⟨ty, fl, a, rfl, rfl, rfl, hety, hfl⟩ := inv_atomicLoad_root hdat
  repeat (mem_inv_simp [] at * <;> isel_destruct <;> subst_vars)
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hL := ‹ApplyInternal _ _ _ _ 27 422 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨mi, hmi, rfl, hs3⟩ := load_acquire_ok hp hco (by omega) hL
  obtain ⟨rfl, hs'⟩ := output_reg_inv hp ctx hco (by omega) hO
  have := hctx.valueReg a _ ‹ctx.valueReg? a = some _›; subst this
  simp only [‹_ = List.map CTy.ofClif [ty]›, List.map_cons, List.map_nil, List.head?_cons,
    Option.getD_some] at hmi
  rw [ofV_loadAcquire, Option.some.injEq] at hmi
  subst hmi
  simp only at hs' hs3 ⊢
  rw [hs3] at hs'
  subst hs'
  refine ⟨_, ?_, _, rfl, atomicLoad_lower_ok hMR hM hMRo hety hfl (hA64 _ rfl)⟩
  rw [fresh_fst]
  exact (frag_one _ (.loadAcquire _ (.vreg _ .int) (.vreg _ .int) _)
    (by simp [vdefs, operands_loadAcquire, Operand.isDef])).emitted

set_option maxHeartbeats 2000000 in
include hp in
/-- **`atomic_store`** (`lower.isle:2321`, rule id 984): `stlr`. -/
theorem atomic_store_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2321 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [ext_valid_atomic_transaction_iff] at hmatch heval
  have hdat0 := hctx.data _ _ _ hi hic
  have hA64 := fun x => hctx.addr64 _ _ _ x hi hic
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hdat := data_trans hdat0 ‹_›
  obtain ⟨ty, fl, x, a, rfl, hvs, rfl, hety, hfl⟩ := inv_atomicStore_root hdat
  repeat (mem_inv_simp [ext_valid_atomic_transaction_iff] at * <;> isel_destruct <;> subst_vars)
  have hSR := ‹ApplyInternal _ _ _ _ 46 423 _ _ _ _›
  have hSE := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  obtain ⟨rfl, hs4⟩ := store_release_ok hp hco (by omega) hSR
  obtain ⟨mi, hmi, hs', rfl⟩ := side_effect_inst_ok hp hco (ctx := ctx) (by omega) hSE
  have := hctx.valueReg x _ ‹ctx.valueReg? x = some _›; subst this
  have := hctx.valueReg a _ ‹ctx.valueReg? a = some _›; subst this
  rw [ofV_storeRelease, Option.some.injEq] at hmi
  subst hmi
  simp only at hs' hs4 ⊢
  rw [hs4] at hs'
  subst hs'
  refine ⟨_, ?_, _, rfl, atomicStore_lower_ok hMR hM hMRo hety hfl (hA64 _ rfl) ‹_›⟩
  exact (frag_emit0 _ (.storeRelease _ (.vreg _ .int) (.vreg _ .int) _)
    (by simp [vdefs, operands_storeRelease, Operand.isDef])).emitted

include hp in
/-- **`uextend` of an `atomic_load`** (rule id 810): never matches (`is_sinkable_inst` fails). -/
theorem uextend_atomic_load_ok : MemRuleOk F sb syms isem MR env cp p rule_lower_1272 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  mem_inv hp [ctor_is_sinkable_inst] at hmatch

end Roots

/-- A single-pattern `and` matches as its pattern (`atomic_cas`'s root, `(and (atomic_cas …))`). -/
theorem matchPat_and_single {p : Program} {ctx : Ctx} {st : LState} {ty : TypeId} {q : Pattern}
    {v : V} {env : Interp.Env V} :
    matchPat p (sem ctx) st (.and ty [q]) v env = matchPat p (sem ctx) st q v env := by
  rw [matchPat.eq_7, matchAll.eq_2]
  cases matchPat p (sem ctx) st q v env with
  | error e => rfl
  | ok o => cases o <;> rfl

theorem ext_value_array_3_iff (ctx : Ctx) (st : LState) (a b c : Nat) (fs : List V) :
    externExtract ctx T.value_array_3 (.values [a, b, c]) st = .ok fs ↔
      fs = [.value a, .value b, .value c] := by
  have : externExtract ctx T.value_array_3 (.values [a, b, c]) st =
    .ok [.value a, .value b, .value c] := rfl
  rw [this]; simp [eq_comm]

theorem ofV_casLoop (t : CTy) (fl : Clif.MemFlags) (a e x d d1 : Reg) :
    MInst.ofV (.data 58 38 [.ty t, .op (.memFlags fl), .reg a, .reg e, .reg x, .reg d, .reg d1]) =
      some (.atomicCasLoop t fl a e x d d1) := rfl

/-- The proof of an `atomic_rmw` root rule (`lower.isle:2357`–`2377`): the instruction is an
`atomic_rmw` of the rule's operation, lowered to `AtomicRMWLoop` (`atomicRmw_lower_ok`). -/
syntax "rmw_root" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rmw_root) => `(tactic| (
    intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
    mem_inv hp [ext_valid_atomic_transaction_iff] at hmatch heval
    have hdat0 := hctx.data _ _ _ hi hic
    have hA64 := fun x => hctx.addr64 _ _ _ x hi hic
    have hRT := hctx.resTys _ _ _ hi hic
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    have hdat := data_trans hdat0 ‹_›
    obtain ⟨cop, ty, fl, a, x, nm, rfl, hvs, rfl, hnm, hk, hety, hfl⟩ := inv_atomicRmw_root hdat
    cases cop <;> simp only [rmwOpName, Option.some.injEq] at hnm <;> subst hnm <;>
      (try (exact absurd hk (by decide)))
    repeat (mem_inv_simp [ext_value_array_2_iff] at * <;> isel_destruct <;> subst_vars)
    simp only [Clif.Inst.resultTypes, Option.some.injEq] at *
    isel_destruct; subst_vars
    have hL := ‹ApplyInternal _ _ _ _ 27 612 _ _ _ _›
    have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
    obtain ⟨mi, hmi, rfl, hs3⟩ := atomic_rmw_loop_ok hp hco (by omega) hL
    obtain ⟨rfl, hs'⟩ := output_reg_inv hp ctx hco (by omega) hO
    have := hctx.valueReg a _ ‹ctx.valueReg? a = some _›; subst this
    have := hctx.valueReg x _ ‹ctx.valueReg? x = some _›; subst this
    simp only [‹_ = List.map CTy.ofClif [ty]›, List.map_cons, List.map_nil, List.head?_cons,
      Option.getD_some] at hmi
    obtain rfl := Option.some.inj (hmi.symm.trans rfl)
    simp only at hs' hs3 ⊢
    rw [hs3] at hs'
    subst hs'
    refine ⟨_, ?_, _, rfl, atomicRmw_lower_ok hMR hM hMRo (by rfl) hety hfl (hA64 _ rfl)⟩
    simp only [LState.fresh]
    exact (frag_fresh3 _ (.atomicRmwLoop _ _ _ (.vreg _ .int) (.vreg _ .int) (.vreg _ .int)
      (.vreg _ .int) (.vreg _ .int)) (by simp [vdefs, operands_rmwLoop, Operand.isDef])).emitted))

section LoopRoots
variable {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {sb : Nat}
  {syms : String → Option Nat} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_rmw` `add`** (`lower.isle:2357`). -/
theorem atomic_rmw_add_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2357 := by
  rmw_root

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_rmw` `sub`** (`lower.isle:2359`). -/
theorem atomic_rmw_sub_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2359 := by
  rmw_root

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_rmw` `and`** (`lower.isle:2361`). -/
theorem atomic_rmw_and_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2361 := by
  rmw_root

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_rmw` `nand`** (`lower.isle:2363`). -/
theorem atomic_rmw_nand_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2363 := by
  rmw_root

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_rmw` `or`** (`lower.isle:2365`). -/
theorem atomic_rmw_or_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2365 := by
  rmw_root

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_rmw` `xor`** (`lower.isle:2367`). -/
theorem atomic_rmw_xor_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2367 := by
  rmw_root

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_rmw` `smin`** (`lower.isle:2369`). -/
theorem atomic_rmw_smin_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2369 := by
  rmw_root

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_rmw` `smax`** (`lower.isle:2371`). -/
theorem atomic_rmw_smax_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2371 := by
  rmw_root

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_rmw` `umin`** (`lower.isle:2373`). -/
theorem atomic_rmw_umin_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2373 := by
  rmw_root

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_rmw` `umax`** (`lower.isle:2375`). -/
theorem atomic_rmw_umax_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2375 := by
  rmw_root

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_rmw` `xchg`** (`lower.isle:2377`). -/
theorem atomic_rmw_xchg_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2377 := by
  rmw_root

set_option maxHeartbeats 4000000 in
include hp in
/-- **`atomic_cas`** (`lower.isle:2390`, rule id 1007): `AtomicCASLoop`. -/
theorem atomic_cas_ok (hMR : MRStable F MR) (hM : MemRefines F sb syms isem) :
    MemRuleOk F sb syms isem MR env cp p rule_lower_2390 := by
  intro f ctx hctx hMRo ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  mem_inv hp [ext_valid_atomic_transaction_iff, matchPat_and_single] at hmatch heval
  have hdat0 := hctx.data _ _ _ hi hic
  have hA64 := fun x => hctx.addr64 _ _ _ x hi hic
  have hRT := hctx.resTys _ _ _ hi hic
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hdat := data_trans hdat0 ‹_›
  obtain ⟨ty, fl, a, e, x, rfl, hvs, rfl, hety, hfl⟩ := inv_atomicCas_root hdat
  repeat (mem_inv_simp [ext_value_array_3_iff] at * <;> isel_destruct <;> subst_vars)
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hL := ‹ApplyInternal _ _ _ _ 27 613 _ _ _ _›
  have hO := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨mi, hmi, rfl, hs3⟩ := atomic_cas_loop_ok hp hco (by omega) hL
  obtain ⟨rfl, hs'⟩ := output_reg_inv hp ctx hco (by omega) hO
  have := hctx.valueReg a _ ‹ctx.valueReg? a = some _›; subst this
  have := hctx.valueReg e _ ‹ctx.valueReg? e = some _›; subst this
  have := hctx.valueReg x _ ‹ctx.valueReg? x = some _›; subst this
  simp only [‹_ = List.map CTy.ofClif [ty]›, List.map_cons, List.map_nil, List.head?_cons,
    Option.getD_some] at hmi
  rw [ofV_casLoop, Option.some.injEq] at hmi
  subst hmi
  simp only at hs' hs3 ⊢
  rw [hs3] at hs'
  subst hs'
  refine ⟨_, ?_, _, rfl, atomicCas_lower_ok hMR hM hMRo hety hfl (hA64 _ rfl)⟩
  simp only [LState.fresh]
  exact (frag_fresh2 _ (.atomicCasLoop _ _ (.vreg _ .int) (.vreg _ .int) (.vreg _ .int)
    (.vreg _ .int) (.vreg _ .int)) (by simp [vdefs, operands_casLoop, Operand.isDef])).emitted

end LoopRoots

/-! ## `MemRulesCorrect` -/

/-- The memory root rules of `lower`, in order. -/
theorem lower_memRoot_filter : (program.rulesOf TId.lower).filter memRootRule =
    [rule_lower_1272, rule_lower_1300, rule_lower_1359, rule_lower_2316, rule_lower_2321, rule_lower_2357, rule_lower_2359, rule_lower_2361, rule_lower_2363, rule_lower_2365, rule_lower_2367, rule_lower_2369, rule_lower_2371, rule_lower_2373, rule_lower_2375, rule_lower_2377, rule_lower_2390, rule_lower_2486, rule_lower_2491, rule_lower_2604, rule_lower_2607, rule_lower_2610, rule_lower_2613, rule_lower_2647, rule_lower_2650, rule_lower_2653, rule_lower_2656, rule_lower_2659, rule_lower_2662, rule_lower_2705, rule_lower_2709, rule_lower_2713, rule_lower_2717, rule_lower_2722, rule_lower_2726, rule_lower_2730, rule_lower_2849, rule_lower_3217, rule_lower_3220] := by
  rw [program_rulesOf_686]
  rfl

/-- **The memory family (M4)**: every memory root rule of `lower` is correct under
`MemRefines`, for every function whose memory relation is `MemRelOk`. -/
theorem memRulesCorrect_program : MemRulesCorrect program := by
  intro F sb syms isem MR env cp hR hMR hM r hr hmem
  have hsub : r ∈ (program.rulesOf TId.lower).filter memRootRule := List.mem_filter.2 ⟨hr, hmem⟩
  rw [lower_memRoot_filter] at hsub
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hsub
  rcases hsub with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact uextend_atomic_load_ok data_program
  · exact uextend_load_ok data_program
  · exact sextend_load_ok data_program
  · exact atomic_load_ok data_program hMR hM
  · exact atomic_store_ok data_program hMR hM
  · exact atomic_rmw_add_ok data_program hMR hM
  · exact atomic_rmw_sub_ok data_program hMR hM
  · exact atomic_rmw_and_ok data_program hMR hM
  · exact atomic_rmw_nand_ok data_program hMR hM
  · exact atomic_rmw_or_ok data_program hMR hM
  · exact atomic_rmw_xor_ok data_program hMR hM
  · exact atomic_rmw_smin_ok data_program hMR hM
  · exact atomic_rmw_smax_ok data_program hMR hM
  · exact atomic_rmw_umin_ok data_program hMR hM
  · exact atomic_rmw_umax_ok data_program hMR hM
  · exact atomic_rmw_xchg_ok data_program hMR hM
  · exact atomic_cas_ok data_program hMR hM
  · exact func_addr_ok data_program faData_program hR hMR hM
  · exact symbol_value_ok data_program hR hMR hM
  · exact load_i8_ok data_program hR hMR hM
  · exact load_i16_ok data_program hR hMR hM
  · exact load_i32_ok data_program hR hMR hM
  · exact load_i64_ok data_program hR hMR hM
  · exact uload8_ok data_program hR hMR hM
  · exact sload8_ok data_program hR hMR hM
  · exact uload16_ok data_program hR hMR hM
  · exact sload16_ok data_program hR hMR hM
  · exact uload32_ok data_program hR hMR hM
  · exact sload32_ok data_program hR hMR hM
  · exact store_i8_ok data_program hR hMR hM
  · exact store_i16_ok data_program hR hMR hM
  · exact store_i32_ok data_program hR hMR hM
  · exact store_i64_ok data_program hR hMR hM
  · exact istore8_ok data_program hR hMR hM
  · exact istore16_ok data_program hR hMR hM
  · exact istore32_ok data_program hR hMR hM
  · exact stack_addr_ok data_program hMR hM
  · exact tls_value_ok data_program hMR hM
  · exact tls_value_macho_ok data_program

end Backend.Proof
