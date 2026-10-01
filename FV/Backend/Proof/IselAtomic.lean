import FV.Backend.Proof.IselMemFuncAddr
import FV.Backend.Proof.IselCmpCond
import FV.Backend.Proof.IselFamAluBShiftTerms

/-!
# `bmask`, the atomics and `fence` (agent/atomics-proof)

The root rules of `lower` for `bmask` (rule id 936, `lower_bmask`: `cmp #0` + `csetm ne`, the
subwords masked first), `fence` (1024, `dmb ish`), `atomic_load` (983, `ldar`), `atomic_store`
(984, `stlr`), `atomic_rmw` (994–1004, one per operation: the LL/SC pseudo-instruction
`AtomicRMWLoop`), `atomic_cas` (1007, `AtomicCASLoop`), and the `uextend` of an `atomic_load`
(810, never matches: `is_sinkable_inst` fails). `bmask` and `fence` are `LowerRuleOk`; the
atomics are memory rules (`MemRuleOk`, under `MemRefines`' atomic clauses). The CLIF semantics
is single-threaded (`Clif.evalInst`: a load, a store, or a load then a store).

`memRulesCorrect_program` collects every memory root rule.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Helper terms -/

section Helpers
variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

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
    (hp64 : ctx.valueType? p = some (.int 64)) :
    LowerInstOk isem MR env cp ctx (.atomicStore ty fl x p) results st []
      (st.emit (.storeRelease (CTy.ofClif ty) (.vreg x .int) (.vreg p .int) fl))
      [.storeRelease (CTy.ofClif ty) (.vreg x .int) (.vreg p .int) fl] := by
  have hfr := frag_emit0 st (.storeRelease (CTy.ofClif ty) (.vreg x .int) (.vreg p .int) fl)
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
  obtain ⟨w2, o1, o2, hs, hsw⟩ := hM.2.2.2.2.2.2.1 (CTy.ofClif ty) op fl p x st.nextVreg
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
        [ofX ((Arm.read_mem_bytes (CTy.ofClif ty).bytes (lo64 (ρ p)) w).setWidth 64), o1, o2] ρ
        st.nextVreg = ofX ((Arm.read_mem_bytes (CTy.ofClif ty).bytes (lo64 (ρ p)) w).setWidth 64) := by
      simp [vdefUpd, writeV, Operand.isDef, Operand.isEarly, Operand.isLate, upd]
    rw [e]
    exact atom_holds hety (ofClif_bytes_width hety) hbits
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

end Builders

end Backend.Proof
