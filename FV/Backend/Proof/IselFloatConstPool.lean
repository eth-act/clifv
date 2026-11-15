import FV.Backend.Proof.IselLowerAll

/-!
# The literal-pool `f64const` (#1002 part 2)

`constant_f64`'s last rule (`inst.isle:4275`) loads a 64-bit pattern that none of its earlier
rules builds (not zero, not an `fmov` immediate, not below `2^32`, low 32 bits not zero) from the
function's constant pool: `fpu_load64 (AMode.Const (emit_u64_le_const n)) (mem_flags_trusted)`,
`ldr d, <entry>` (`MInst.fpuLoad .size64 _ (.const n) trustedFlags`, #565). Its value is the
entry's when the VCode semantics gives the literal-pool load the entry's value
(`PoolRefinesFP`, a part of `MemRefinesFP`): `csem` does (`E2E.poolRefinesFP_csem`, `mspec`'s pool
clause), and the register-level proof reads the entry from the function's code
(`E2E.RegLevelPool`).

* `fpu_load64_ok`: the internal term `fpu_load64` (`inst.isle:5548`) emits `ldr d` into a fresh
  float vreg;
* `fconst_pool`: the pool load's `FConstOut` under `PoolRefinesFP`;
* `constant_f64_okL`: `constant_f64` of every 64-bit pattern (`constant_f64_ok` is stated for
  the patterns without literal pool, `hpf`);
* `f64const_okTL`: the `f64const` root (`rule_lower_68`, rule 585) on every `f64const`
  (`f64const_okT` is stated for `F64PoolFreeInst`);
* `LowerRulesCorrectTL`, `lowerRulesCorrectTL_program`: the float data-movement roots
  (`floatMoveRootRule`) correct on every instruction of a float-capable context under
  `Refines` and `PoolRefinesFP` (`LowerRulesCorrectT`'s first part without `F64PoolFreeInst`).

Generated code is unchanged: these are the proofs of the shipped lowering.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Running the literal-pool load -/

section Run
variable {F : BitVec 64 → Prop} {isem : Sem}

/-- `prun_cons` for an instruction whose semantics is given directly (not through `ispec` and
`Refines`): it returns `outs` and `next` with a world that agrees with the start. -/
theorem prun_cons_sem {i : MInst} {ms : List MInst} {ρ ρ' : Nat → CV}
    {ops : Array Operand} {outs : List CV} (hops : i.operands = .ok ops)
    (hs : ∀ w, ∃ w', isem i (vuses ops ρ) w = some (outs, w', .next) ∧ SameWorld F w' w)
    (hlen : outs.length = (ops.toList.filter Operand.isDef).length)
    (ht : PRun F isem ms (vdefUpd ops outs ρ) ρ') : PRun F isem (i :: ms) ρ ρ' := by
  intro w
  obtain ⟨w1, h1, s1⟩ := hs w
  obtain ⟨w2, h2, s2⟩ := ht w1
  refine ⟨w2, ?_, s2.trans' s1⟩
  simp only [seqRun, hops, h1, hlen, ↓reduceIte, h2, Option.map_some]
  rfl

/-- **The literal-pool load of `c` into a fresh float vreg** (`ldr d, <entry>`): under
`PoolRefinesFP` its def holds `c`'s 64 bits, zero-extended. -/
theorem fconst_pool (hpool : PoolRefinesFP F isem) (st : LState) (c : Nat) (fl : Clif.MemFlags) :
    FConstOut F isem 64 c st
      ((st.fresh .float).2.emit (.fpuLoad .size64 (st.fresh .float).1 (.const c) fl))
      (.reg (st.fresh .float).1) := by
  have e : (st.fresh .float).1 = .vreg st.nextVreg .float := by simp [LState.fresh]
  rw [e]
  have hops : (MInst.fpuLoad .size64 (.vreg st.nextVreg .float) (.const c) fl).operands =
      .ok #[⟨st.nextVreg, .float, .def, .late, .reg⟩] := by
    simp [MInst.operands, MInst.visitOperands, AMode.visit, StateT.run, pure, StateT.pure,
      Except.pure, bind, StateT.bind, Except.bind, modify, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, OpSpec.def_]
  have hd : vdefs (.fpuLoad .size64 (.vreg st.nextVreg .float) (.const c) fl) = [st.nextVreg] := by
    simp [vdefs, hops, Operand.isDef]
  have hu : vuseNums (.fpuLoad .size64 (.vreg st.nextVreg .float) (.const c) fl) = [] := by
    simp [vuseNums, hops, Operand.isUse]
  refine ⟨[.fpuLoad .size64 (.vreg st.nextVreg .float) (.const c) fl], st.nextVreg, rfl,
    ⟨by simp [LState.emit, LState.fresh], by simp [LState.emit, LState.fresh], Nat.le_refl _, ?_, ?_⟩,
    fun ρ => ⟨upd ρ st.nextVreg ((BitVec.ofNat (ScalarSize.size64.bytes * 8) c).setWidth 128),
      prun_cons_sem hops (fun w => hpool .size64 st.nextVreg c fl w (.inr rfl)) rfl (prun_nil _),
      ?_⟩⟩
  · intro mi hmi d' hd'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
    subst hmi
    simp only [hd, List.mem_cons, List.mem_nil_iff, or_false] at hd'
    subst hd'
    simp [LState.emit, LState.fresh]
  · intro mi hmi u hu'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
    subst hmi
    simp [hu] at hu'
  · simp [upd] <;> rfl

end Run

/-! ## `fpu_load64` -/

section Terms
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 2000000 in
include hp hc in
/-- **`fpu_load64`** (`inst.isle:5548`): a fresh float destination and `ldr d`. -/
theorem fpu_load64_ok {n : Nat} (hn : 40 ≤ n) {a b : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 681 [a, b] s v s') :
    EmitOutC .float s.1 s'.1 v (fun rd => .data 58 61 [.reg rd, a, b]) := by
  isel_split hp hc h 681
  isel_inv [*, rule_inst_5548, ctor_emit_iff, ctor_writable_reg_to_reg'] at hm he
  obtain ⟨rfl, rfl⟩ :=
    (ctor_temp_writable_reg_i8x16_iff ctx _ _ _).mp ‹externCtor ctx T.temp_writable_reg _ _ = _›
  exact ⟨rfl, _, ‹_›, rfl⟩

end Terms

/-- `mem_flags_trusted_data` (`MemFlagsData::trusted()`) is `trustedFlags`, the state unchanged. -/
theorem ctor_mem_flags_trusted_data (ctx : Ctx) (st : LState) :
    externCtor ctx T.mem_flags_trusted_data [] st = .ok (.op (.memFlags trustedFlags), st) :=
  rfl

/-- The `ldr d` of a constant-pool entry. -/
theorem ofV_fpuLoad64Const {r : Reg} {c : Nat} {m : MInst}
    (h : MInst.ofV (.data 58 61 [.reg r, .data 89 12 [.op (.vcodeConst c)],
      .op (.memFlags trustedFlags)]) = some m) :
    m = .fpuLoad .size64 r (.const c) trustedFlags := Option.some.inj (h.symm.trans rfl)

/-! ## `constant_f64` of every pattern -/

section Const
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)
  {F : BitVec 64 → Prop} {isem : Sem}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
include hp hc in
/-- **`constant_f64`** (`inst.isle:4264–4276`) of every 64-bit pattern: `constant_f64_ok`'s four
rules, and the literal pool (`ldr d, <entry>` of `emit_u64_le_const n`, `fconst_pool`) under
`PoolRefinesFP`. -/
theorem constant_f64_okL (hR : Refines F isem) (hpool : PoolRefinesFP F isem) {N : Nat}
    (hN : 300 ≤ N) {i : Int} (hi0 : 0 ≤ i) (hi : i < 2 ^ 64) {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg N 27 587 [.int i] s v s') :
    FConstOut F isem 64 (u64 i) s.1 s'.1 v := by
  have hp' := hp
  have hu64 : u64 i = i.toNat := by unfold u64; omega
  isel_split hp hc h 587
  all_goals isel_inv [*, rule_inst_4264, rule_inst_4268, rule_inst_4271, rule_inst_4273,
    rule_inst_4275] at hm he
  · -- `0`: `movi vd.2s, #0`
    obtain ⟨rfl, rfl⟩ :=
      (ctor_mov_mod_imm_zero32_iff ctx _ _ _).mp ‹externCtor ctx T.asimd_mov_mod_imm_zero _ _ = _›
    have h1 := ‹ApplyInternal _ _ _ _ 27 375 _ _ _ _›
    obtain ⟨rfl, m1, hm1, hs1⟩ := vec_dup_imm_ok hp' hc (by omega) h1
    obtain rfl := ofV_vecDupImm hm1
    simp only at hs1 ⊢
    rw [hs1]
    exact fconst_one hR rfl (fun w => rfl) (by simp [moviVal_zero, movModImmZero]; rfl) rfl rfl
  · -- an `fmov d` immediate
    obtain ⟨mm, hmm, rfl, rfl⟩ :=
      (ctor_fp_mod_imm64_iff ctx _ _ _ _).mp ‹externCtor ctx T.asimd_fp_mod_imm_from_u64 _ _ = _›
    have h1 := ‹ApplyInternal _ _ _ _ 27 411 _ _ _ _›
    obtain ⟨rfl, m1, hm1, hs1⟩ := fpu_move_fp_imm_ok hp' hc (by omega) h1
    obtain rfl := ofV_fpuMoveFPImm64 hm1
    simp only at hs1 ⊢
    rw [hs1]
    refine fconst_one hR rfl (fun w => rfl) ?_ rfl rfl
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [fpModImm64_val hmm, BitVec.toNat_ofNat]
  · -- a pattern that fits 32 bits: `constant_f32`
    obtain ⟨⟨hj0, hj⟩, hfs⟩ :=
      (ext_u32_from_u64_iff ctx _ _ _).mp ‹externExtract ctx T.u32_from_u64 _ _ = _›
    simp only [List.cons.injEq, and_true] at hfs
    subst hfs
    have h1 := ‹ApplyInternal _ _ _ _ 27 586 _ _ _ _›
    have h32 := constant_f32_ok hp' hc hR (by omega) hj0 hj h1
    exact h32.widen (by omega)
  · -- low 32 bits clear: `fmov d, x` of the `imm` sequence
    obtain ⟨hlow, hfs⟩ :=
      (ext_u64_low32_bits_unset_iff ctx _ _ _).mp ‹externExtract ctx T.u64_low32_bits_unset _ _ = _›
    simp only [List.cons.injEq, and_true] at hfs
    subst hfs
    have h1 := ‹ApplyInternal _ _ _ _ 27 553 _ _ _ _›
    obtain ⟨ms, d1, rfl, hsh, hrun⟩ :=
      imm_ok_ai hp' hc hR (.inr (.inr (.inr rfl))) (.inr rfl) (by omega) h1
    have h2 := ‹ApplyInternal _ _ _ _ 27 409 _ _ _ _›
    obtain ⟨k', hk', rfl, m1, hm1, hs1⟩ := mov_to_fpu_any_ok hp' hc (by omega) h2
    obtain rfl : k' = 3 := by rcases hk' with h | ⟨h, -⟩ <;> omega
    obtain rfl := ofV_movToFpu64 hm1
    simp only at hs1 hsh ⊢
    rw [hs1]
    refine fconst_snoc hR hsh rfl (fun ρ => ?_) rfl rfl
    obtain ⟨ρ', X, hp, hx, hX, -⟩ := hrun ρ
    refine ⟨ρ', _, hp, fun w => rfl, ?_⟩
    rw [hx]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · -- the literal pool (#1002 part 2): `ldr d, <entry>` of the entry `emit_u64_le_const n`
    have hk1 := ‹externCtor ctx T.emit_u64_le_const _ _ = _›
    rw [ctor_emit_u64_le_const_ne] at hk1
    simp only [ExtResult.ok.injEq, Prod.mk.injEq] at hk1
    obtain ⟨rfl, rfl⟩ := hk1
    have hk2 := ‹externCtor ctx T.mem_flags_trusted_data _ _ = _›
    rw [ctor_mem_flags_trusted_data] at hk2
    simp only [ExtResult.ok.injEq, Prod.mk.injEq] at hk2
    obtain ⟨rfl, rfl⟩ := hk2
    have h1 := ‹ApplyInternal _ _ _ _ 27 681 _ _ _ _›
    obtain ⟨rfl, m1, hm1, hs1⟩ := fpu_load64_ok hp' hc (by omega) h1
    obtain rfl := ofV_fpuLoad64Const hm1
    simp only at hs1 ⊢
    rw [hs1]
    exact fconst_pool hpool _ _ _

end Const

/-! ## The `f64const` root on every `f64const` -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`f64const`** (`rule_lower_68`, `lower.isle:68`, rule 585): `constant_f64` of the literal's
bits (`u64_from_ieee64`) into a fresh float vreg, for every `f64const` (#1002 part 2: the literal
pool under `PoolRefinesFP`; `f64const_okT` is stated for `F64PoolFreeInst`). -/
theorem f64const_okTL {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem}
    (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem)
    (hMR : MRStable F MR) (hpool : PoolRefinesFP F isem) :
    LowerRuleOkT isem MR env cp p rule_lower_68 := by
  intro f ctx hctx ii info inst hi hic _ cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 500 := ⟨n - 500, by omega⟩
  obtain ⟨info', fs, hi', hd⟩ := root_match_data hp ctx (r := rule_lower_68) rfl hp.t2481
    term_2481_kind hp.t2344 term_2344_kind (m := m' + 9) hmatch
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hic
  rw [hd] at hdat
  obtain ⟨imm, rfl, rfl⟩ := instData_f64const_inv hdat
  have hp' := hp
  isel_inv' hp [] at hmatch heval
  obtain ⟨rfl, rfl⟩ := fconst_data_eq hi hd ‹ctx.insts[ii]? = some _› ‹V.data 152 34 _ = _›
  have hfs := (ext_u64_from_ieee64_iff ctx _ _ _).mp ‹externExtract ctx T.u64_from_ieee64 _ _ = _›
  simp only [List.cons.injEq, and_true] at hfs
  subst hfs
  have h1 := ‹ApplyInternal _ _ _ _ 27 587 _ _ _ _›
  have hlt := imm.isLt
  obtain ⟨ms, d, rfl, hsh, hrun⟩ :=
    constant_f64_okL hp' hco hR hpool (by omega) (by omega) (by have h := hlt; simp at h; omega) h1
  have h2 := ‹ApplyInternal _ _ _ _ 25 172 _ _ _ _›
  obtain ⟨rfl, hs2⟩ := output_reg_ok hp' hco (by omega) h2
  try simp only at hs2
  subst hs2
  have hu : u64 (imm.toNat : Int) = imm.toNat := by unfold u64; omega
  rw [hu] at hrun
  first
    | refine ⟨ms, hsh.emitted, [[.vreg d .float]], rfl, ?_⟩
    | refine ⟨ms, [[.vreg d .float]], hsh.emitted, rfl, ?_⟩
  exact lowerInstOk_fconst hMR hsh hrun (by decide)

/-! ## The float data-movement roots with the literal pool -/

/-- **The float data-movement roots with the literal pool** (#1002 part 2): over float-capable
contexts, under `Refines` and the literal-pool load's semantics (`PoolRefinesFP`), the
`f32const`/`f64const`/`bitcast` roots (`floatMoveRootRule`) are correct on every instruction
(`LowerRulesCorrectT`'s first part, which states the `f64const` root for `F64PoolFreeInst`). -/
def LowerRulesCorrectTL (p : Program) : Prop :=
  ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program),
    Refines F isem → MRStable F MR → PoolRefinesFP F isem →
    ∀ r ∈ p.rulesOf TId.lower, floatMoveRootRule r = true → LowerRuleOkT isem MR env cp p r

/-- **`LowerRulesCorrectTL` holds for the exported program.** -/
theorem lowerRulesCorrectTL_program : LowerRulesCorrectTL program := by
  intro F isem MR env cp hR hMR hpool r hr hfm
  have hp := data_program
  have hsub : r ∈ (program.rulesOf TId.lower).filter floatMoveRootRule :=
    List.mem_filter.2 ⟨hr, hfm⟩
  rw [lower_floatMoveRoot_filter] at hsub
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hsub
  rcases hsub with rfl | rfl | rfl | rfl | rfl | rfl
  · exact bitcast_fp_fp_okT hp MR env cp
  · exact bitcast_gpr_fp_okT hp MR env cp hR hMR
  · exact bitcast_fp_gpr_okT hp MR env cp hR hMR
  · exact bitcast_gpr_gpr_okT hp MR env cp
  · exact f32const_okT hp MR env cp hR hMR
  · exact f64const_okTL hp MR env cp hR hMR hpool

end Backend.Proof
