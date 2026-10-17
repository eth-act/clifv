import FV.Backend.Proof.IselFloatBitcast
import FV.Backend.Proof.IselCmpDiv

/-!
# S11e4: `f32const`/`f64const` over float-capable contexts

The roots `rule_lower_63` (584, `f32const`) and `rule_lower_68` (585, `f64const`) put the
literal's bit pattern (`u32_from_ieee32`/`u64_from_ieee64`) through `constant_f32`/
`constant_f64` (`inst.isle:4242–4275`):

* `0` → `movi vd.2s, #0` (`vec_dup_imm` of `asimd_mov_mod_imm_zero`), which zeroes the
  register;
* an `fmov` immediate (`asimd_fp_mod_imm_from_u64`) → `fmov s/d, #imm`, whose value
  `VFPExpandImm` is the literal (`vfpExpand32_eq`/`vfpExpand64_eq`, all 256 encodings,
  `decide +kernel`);
* an `f64` whose bits fit 32 bits → `constant_f32` of them (the upper half of the register is
  zero);
* an `f64` whose low 32 bits are zero → `fmov d, x` of the `imm` sequence;
* otherwise `f32` → `fmov s, w` of the `imm` sequence, and `f64` → the literal pool
  (`emit_u64_le_const`, not modelled: the lowering fails, so a matched evaluation never takes
  this rule).

`constant_f16` (`u16_from_u32` with `use_fp16`) is off (`use_fp16` is `false`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Extern facts -/

section Ext
variable (ctx : Ctx) (st : LState)

theorem ext_u32_from_ieee32_iff (i : Int) (fs : List V) :
    externExtract ctx T.u32_from_ieee32 (.int i) st = .ok fs ↔ fs = [.int i] := by
  have : externExtract ctx T.u32_from_ieee32 (.int i) st = .ok [.int i] := rfl
  rw [this]; simp only [ExtResult.ok.injEq]; exact eq_comm

theorem ext_u64_from_ieee64_iff (i : Int) (fs : List V) :
    externExtract ctx T.u64_from_ieee64 (.int i) st = .ok fs ↔ fs = [.int i] := by
  have : externExtract ctx T.u64_from_ieee64 (.int i) st = .ok [.int i] := rfl
  rw [this]; simp only [ExtResult.ok.injEq]; exact eq_comm

theorem ext_u16_from_u32_iff (i : Int) (fs : List V) :
    externExtract ctx T.u16_from_u32 (.int i) st = .ok fs ↔ (0 ≤ i ∧ i < 2 ^ 16) ∧ fs = [.int i] := by
  have : externExtract ctx T.u16_from_u32 (.int i) st =
      if 0 ≤ i ∧ i < 2 ^ 16 then .ok [.int i] else .fail := rfl
  rw [this]; clear this
  split
  · rename_i h; simp only [h, ExtResult.ok.injEq, true_and]; exact eq_comm
  · rename_i h; simp only [h, reduceCtorEq, false_and]

theorem ext_u32_from_u64_iff (i : Int) (fs : List V) :
    externExtract ctx T.u32_from_u64 (.int i) st = .ok fs ↔ (0 ≤ i ∧ i < 2 ^ 32) ∧ fs = [.int i] := by
  have : externExtract ctx T.u32_from_u64 (.int i) st =
      if 0 ≤ i ∧ i < 2 ^ 32 then .ok [.int i] else .fail := rfl
  rw [this]; clear this
  split
  · rename_i h; simp only [h, ExtResult.ok.injEq, true_and]; exact eq_comm
  · rename_i h; simp only [h, reduceCtorEq, false_and]

theorem ext_u64_low32_bits_unset_iff (i : Int) (fs : List V) :
    externExtract ctx T.u64_low32_bits_unset (.int i) st = .ok fs ↔
      u64 i % 2 ^ 32 = 0 ∧ fs = [.int i] := by
  have : externExtract ctx T.u64_low32_bits_unset (.int i) st =
      if u64 i % 2 ^ 32 = 0 then .ok [.int i] else .fail := rfl
  rw [this]; clear this
  split
  · rename_i h; simp only [h, ExtResult.ok.injEq, true_and]; exact eq_comm
  · rename_i h; simp only [h, reduceCtorEq, false_and]

theorem ctor_u32_into_u64_iff (i : Int) (v : V) (st' : LState) :
    externCtor ctx T.u32_into_u64 [.int i] st = .ok (v, st') ↔ v = .int i ∧ st' = st := by
  have : externCtor ctx T.u32_into_u64 [.int i] st = .ok (.int i, st) := rfl
  rw [this]
  simp only [ExtResult.ok.injEq, Prod.mk.injEq]
  exact ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩

theorem ctor_mov_mod_imm_zero32_iff (v : V) (st' : LState) :
    externCtor ctx T.asimd_mov_mod_imm_zero [.data 95 2 []] st = .ok (v, st') ↔
      v = .op (.movModImm (movModImmZero .size32)) ∧ st' = st := by
  have : externCtor ctx T.asimd_mov_mod_imm_zero [.data 95 2 []] st =
      .ok (.op (.movModImm (movModImmZero .size32)), st) := rfl
  rw [this]
  simp only [ExtResult.ok.injEq, Prod.mk.injEq]
  exact ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩

theorem ctor_fp_mod_imm32_iff (i : Int) (v : V) (st' : LState) :
    externCtor ctx T.asimd_fp_mod_imm_from_u64 [.int i, .data 95 2 []] st = .ok (v, st') ↔
      ∃ m, fpModImm? (u64 i) .size32 = some m ∧ v = .op (.fpModImm m) ∧ st' = st := by
  have : externCtor ctx T.asimd_fp_mod_imm_from_u64 [.int i, .data 95 2 []] st =
      match (fpModImm? (u64 i) .size32).map (V.op ∘ Opnd.fpModImm) with
      | some v => .ok (v, st)
      | none => .fail := rfl
  rw [this]
  cases fpModImm? (u64 i) .size32 <;> simp [eq_comm]

theorem ctor_fp_mod_imm64_iff (i : Int) (v : V) (st' : LState) :
    externCtor ctx T.asimd_fp_mod_imm_from_u64 [.int i, .data 95 3 []] st = .ok (v, st') ↔
      ∃ m, fpModImm? (u64 i) .size64 = some m ∧ v = .op (.fpModImm m) ∧ st' = st := by
  have : externCtor ctx T.asimd_fp_mod_imm_from_u64 [.int i, .data 95 3 []] st =
      match (fpModImm? (u64 i) .size64).map (V.op ∘ Opnd.fpModImm) with
      | some v => .ok (v, st)
      | none => .fail := rfl
  rw [this]
  cases fpModImm? (u64 i) .size64 <;> simp [eq_comm]

/-- The literal pool is not modelled: `emit_u64_le_const` never returns. -/
theorem ctor_emit_u64_le_const_ne (i : Int) (v : V) (st' : LState) :
    externCtor ctx T.emit_u64_le_const [.int i] st ≠ .ok (v, st') := by
  have : externCtor ctx T.emit_u64_le_const [.int i] st =
      .unmodeled s!"constructor {T.emit_u64_le_const.name} ({[V.int i].length} args)" := rfl
  rw [this]; exact fun h => by cases h

end Ext

/-! ## Internal terms -/

section Terms
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

set_option maxHeartbeats 2000000 in
include hp hc in
theorem vec_dup_imm_ok {n : Nat} (hn : 40 ≤ n) {a b c : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 375 [a, b, c] s v s') :
    EmitOutC .float s.1 s'.1 v (fun rd => .data 58 83 [.reg rd, a, b, c]) := by
  isel_split hp hc h 375
  isel_inv [*, rule_inst_2640, ctor_emit_iff, ctor_writable_reg_to_reg'] at hm he
  obtain ⟨rfl, rfl⟩ :=
    (ctor_temp_writable_reg_i8x16_iff ctx _ _ _).mp ‹externCtor ctx T.temp_writable_reg _ _ = _›
  exact ⟨rfl, _, ‹_›, rfl⟩

set_option maxHeartbeats 2000000 in
include hp hc in
theorem fpu_move_fp_imm_ok {n : Nat} (hn : 40 ≤ n) {a b : V} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 411 [a, b] s v s') :
    EmitOutC .float s.1 s'.1 v (fun rd => .data 58 76 [.reg rd, a, b]) := by
  isel_split hp hc h 411
  isel_inv [*, rule_inst_2948, ctor_emit_iff, ctor_writable_reg_to_reg'] at hm he
  obtain ⟨rfl, rfl⟩ :=
    (ctor_temp_writable_reg_i8x16_iff ctx _ _ _).mp ‹externCtor ctx T.temp_writable_reg _ _ = _›
  exact ⟨rfl, _, ‹_›, rfl⟩

end Terms

/-! ## Values: the `fmov` immediates and the `u64` of a literal -/

/-- `VFPExpandImm` at single precision is `ASIMDFPModImm::value32`, for every encoding. -/
theorem vfpExpand32_table : ∀ j < 256,
    (Arm.DPSFP.VFPExpandImm 8 23 (BitVec.ofNat 8 j)).toNat = fpImmValue32 j := by
  decide +kernel

/-- `VFPExpandImm` at double precision is `ASIMDFPModImm::value64`, for every encoding. -/
theorem vfpExpand64_table : ∀ j < 256,
    (Arm.DPSFP.VFPExpandImm 11 52 (BitVec.ofNat 8 j)).toNat = fpImmValue64 j := by
  decide +kernel

/-- An `fmov s` immediate built for `v` expands to `v`'s low 32 bits. -/
theorem fpModImm32_val {v : Nat} {m : ASIMDFPModImm} (h : fpModImm? v .size32 = some m) :
    (Arm.DPSFP.VFPExpandImm 8 23 m.imm).toNat = v % 2 ^ 32 := by
  simp only [fpModImm?] at h
  split at h
  · rename_i hv
    cases h
    rw [vfpExpand32_table _ (by omega)]
    exact (beq_iff_eq.mp hv).symm
  · cases h

/-- An `fmov d` immediate built for `v` expands to `v`'s low 64 bits. -/
theorem fpModImm64_val {v : Nat} {m : ASIMDFPModImm} (h : fpModImm? v .size64 = some m) :
    (Arm.DPSFP.VFPExpandImm 11 52 m.imm).toNat = v % 2 ^ 64 := by
  simp only [fpModImm?] at h
  split at h
  · rename_i hv
    cases h
    rw [vfpExpand64_table _ (by omega)]
    exact (beq_iff_eq.mp hv).symm
  · cases h

/-! ## The contract of `constant_f32`/`constant_f64` -/

/-- What `constant_f32`/`constant_f64` of `c` returned: a fresh float vreg `d`, defined by code
`ms` that defines only fresh vregs and reads only fresh vregs, holding the `bits`-bit value
`c` zero-extended to 128 bits (a scalar FP write zeroes the rest of the register). -/
def FConstOut (F : BitVec 64 → Prop) (isem : Sem) (bits c : Nat) (st st' : LState) (v : V) : Prop :=
  ∃ ms d, v = .reg (.vreg d .float) ∧ CodeShape st st' ms d st.nextVreg ∧
    ∀ ρ, ∃ ρ', PRun F isem ms ρ ρ' ∧ ρ' d = (BitVec.ofNat bits c).setWidth 128

section Out
variable {F : BitVec 64 → Prop} {isem : Sem}

/-- One instruction defining the fresh float vreg from nothing. -/
theorem fconst_one (hR : Refines F isem) {st : LState} {m : MInst} {r : CV} {bits c : Nat}
    (hops : m.operands = .ok #[⟨st.nextVreg, .float, .def, .late, .reg⟩])
    (hs : ∀ w, ispec m [] w = some ([r], w, .next))
    (hr : r = (BitVec.ofNat bits c).setWidth 128) (hd : vdefs m = [st.nextVreg])
    (hu : vuseNums m = []) :
    FConstOut F isem bits c st ((st.fresh .float).2.emit m) (.reg (st.fresh .float).1) := by
  refine ⟨[m], st.nextVreg, rfl, ⟨by simp [LState.emit, LState.fresh],
    by simp [LState.emit, LState.fresh], Nat.le_refl _, ?_, ?_⟩,
    fun ρ => ⟨upd ρ st.nextVreg r, prun_cons hR hops hs rfl (prun_nil _), ?_⟩⟩
  · intro mi hmi e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
    subst hmi
    simp only [hd, List.mem_cons, List.mem_nil_iff, or_false] at he
    subst he
    simp [LState.emit, LState.fresh]
  · intro mi hmi u hu'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
    subst hmi
    simp [hu] at hu'
  · simp [upd, hr]

/-- Code defining an integer vreg `d1`, then one instruction defining the fresh float vreg
from it. -/
theorem fconst_snoc (hR : Refines F isem) {st st1 : LState} {ms : List MInst} {d1 : Nat}
    {m : MInst} {bits c : Nat} (hsh : CodeShape st st1 ms d1 st.nextVreg)
    (hops : m.operands = .ok #[⟨st1.nextVreg, .float, .def, .late, .reg⟩,
      ⟨d1, .int, .use, .early, .reg⟩])
    (hrun : ∀ ρ, ∃ ρ' r, PRun F isem ms ρ ρ' ∧ (∀ w, ispec m [ρ' d1] w = some ([r], w, .next)) ∧
      r = (BitVec.ofNat bits c).setWidth 128)
    (hd : vdefs m = [st1.nextVreg]) (hu : vuseNums m = [d1]) :
    FConstOut F isem bits c st ((st1.fresh .float).2.emit m) (.reg (st1.fresh .float).1) := by
  refine ⟨ms ++ [m], st1.nextVreg, rfl, ⟨?_, ?_, hsh.mono, ?_, ?_⟩, fun ρ => ?_⟩
  · show st1.emitted.push m = st.emitted ++ (ms ++ [m]).toArray
    rw [hsh.emitted]
    simp
  · simp only [LState.emit, LState.fresh]; have := hsh.mono; omega
  · intro mi hmi e he
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmi
    rcases hmi with hmi | rfl
    · have := hsh.defs mi hmi e he
      simp only [LState.emit, LState.fresh]; omega
    · simp only [hd, List.mem_cons, List.mem_nil_iff, or_false] at he
      subst he
      simp only [LState.emit, LState.fresh]; have := hsh.mono; omega
  · intro mi hmi u hu'
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmi
    rcases hmi with hmi | rfl
    · exact hsh.uses mi hmi u hu'
    · simp only [hu, List.mem_cons, List.mem_nil_iff, or_false] at hu'
      subst hu'
      exact .inl hsh.res
  · obtain ⟨ρ', r, hp, hs, hr⟩ := hrun ρ
    exact ⟨upd ρ' st1.nextVreg r, prun_append hp (prun_cons hR hops hs rfl (prun_nil _)),
      by simp [upd, hr]⟩

/-- A 32-bit constant is the 64-bit one (`constant_f64` through `constant_f32`). -/
theorem FConstOut.widen {st st' : LState} {v : V} {c : Nat} (hc : c < 2 ^ 32)
    (h : FConstOut F isem 32 c st st' v) : FConstOut F isem 64 c st st' v := by
  obtain ⟨ms, d, hv, hsh, hrun⟩ := h
  refine ⟨ms, d, hv, hsh, fun ρ => ?_⟩
  obtain ⟨ρ', hp, hd⟩ := hrun ρ
  refine ⟨ρ', hp, ?_⟩
  rw [hd]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

end Out

/-! ## Decoding the emitted instructions -/

theorem ofV_vecDupImm {r : Reg} {mm : ASIMDMovModImm} {m : MInst}
    (h : MInst.ofV (.data 58 83 [.reg r, .op (.movModImm mm), .bool false, .data 97 4 []]) = some m) :
    m = .vecDupImm r mm false .size32x2 := Option.some.inj (h.symm.trans rfl)

theorem ofV_fpuMoveFPImm32 {r : Reg} {mm : ASIMDFPModImm} {m : MInst}
    (h : MInst.ofV (.data 58 76 [.reg r, .op (.fpModImm mm), .data 95 2 []]) = some m) :
    m = .fpuMoveFPImm r mm .size32 := Option.some.inj (h.symm.trans rfl)

theorem ofV_fpuMoveFPImm64 {r : Reg} {mm : ASIMDFPModImm} {m : MInst}
    (h : MInst.ofV (.data 58 76 [.reg r, .op (.fpModImm mm), .data 95 3 []]) = some m) :
    m = .fpuMoveFPImm r mm .size64 := Option.some.inj (h.symm.trans rfl)

theorem ofV_movToFpu32 {r : Reg} {d : Nat} {m : MInst}
    (h : MInst.ofV (.data 58 75 [.reg r, .reg (.vreg d .int), .data 95 2 []]) = some m) :
    m = .movToFpu r (.vreg d .int) .size32 := Option.some.inj (h.symm.trans rfl)

theorem ofV_movToFpu64 {r : Reg} {d : Nat} {m : MInst}
    (h : MInst.ofV (.data 58 75 [.reg r, .reg (.vreg d .int), .data 95 3 []]) = some m) :
    m = .movToFpu r (.vreg d .int) .size64 := Option.some.inj (h.symm.trans rfl)

/-! ## `constant_f32`, `constant_f64` -/

section Const
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)
  {F : BitVec 64 → Prop} {isem : Sem}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
include hp hc in
/-- **`constant_f32`** (`inst.isle:4242–4252`) of a 32-bit pattern. -/
theorem constant_f32_ok (hR : Refines F isem) {N : Nat} (hN : 200 ≤ N) {i : Int}
    (hi0 : 0 ≤ i) (hi : i < 2 ^ 32) {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg N 27 586 [.int i] s v s') :
    FConstOut F isem 32 (u64 i) s.1 s'.1 v := by
  have hp' := hp
  have hu64 : u64 i = i.toNat := by unfold u64; omega
  isel_split hp hc h 586
  all_goals isel_inv [*, rule_inst_4242, rule_inst_4246, rule_inst_4249, rule_inst_4252] at hm he
  · -- `0`: `movi vd.2s, #0`
    obtain ⟨rfl, rfl⟩ :=
      (ctor_mov_mod_imm_zero32_iff ctx _ _ _).mp ‹externCtor ctx T.asimd_mov_mod_imm_zero _ _ = _›
    have h1 := ‹ApplyInternal _ _ _ _ 27 375 _ _ _ _›
    obtain ⟨rfl, m1, hm1, hs1⟩ := vec_dup_imm_ok hp' hc (by omega) h1
    obtain rfl := ofV_vecDupImm hm1
    simp only at hs1 ⊢
    rw [hs1]
    exact fconst_one hR rfl (fun w => rfl) (by simp [moviVal_zero, movModImmZero]; rfl) rfl rfl
  · -- an `fmov s` immediate
    obtain ⟨rfl, rfl⟩ := (ctor_u32_into_u64_iff ctx _ _ _ _).mp ‹externCtor ctx T.u32_into_u64 _ _ = _›
    obtain ⟨mm, hmm, rfl, rfl⟩ :=
      (ctor_fp_mod_imm32_iff ctx _ _ _ _).mp ‹externCtor ctx T.asimd_fp_mod_imm_from_u64 _ _ = _›
    have h1 := ‹ApplyInternal _ _ _ _ 27 411 _ _ _ _›
    obtain ⟨rfl, m1, hm1, hs1⟩ := fpu_move_fp_imm_ok hp' hc (by omega) h1
    obtain rfl := ofV_fpuMoveFPImm32 hm1
    simp only at hs1 ⊢
    rw [hs1]
    refine fconst_one hR rfl (fun w => rfl) ?_ rfl rfl
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [fpModImm32_val hmm, BitVec.toNat_ofNat]
  · -- `constant_f16`: FP16 is off
    obtain ⟨h1, -⟩ := (ctor_use_fp16_iff ctx _ _ _).mp ‹externCtor ctx T.use_fp16 _ _ = _›
    cases h1
  · -- `fmov s, w` of the `imm` sequence
    obtain ⟨rfl, rfl⟩ := (ctor_u32_into_u64_iff ctx _ _ _ _).mp ‹externCtor ctx T.u32_into_u64 _ _ = _›
    have h1 := ‹ApplyInternal _ _ _ _ 27 553 _ _ _ _›
    obtain ⟨ms, d1, rfl, hsh, hrun⟩ :=
      imm_ok_ai hp' hc hR (.inr (.inr (.inl rfl))) (.inr rfl) (by omega) h1
    have h2 := ‹ApplyInternal _ _ _ _ 27 409 _ _ _ _›
    obtain ⟨k', hk', rfl, m1, hm1, hs1⟩ := mov_to_fpu_any_ok hp' hc (by omega) h2
    obtain rfl : k' = 2 := by rcases hk' with h | ⟨h, -⟩ <;> omega
    obtain rfl := ofV_movToFpu32 hm1
    simp only at hs1 hsh ⊢
    rw [hs1]
    refine fconst_snoc hR hsh rfl (fun ρ => ?_) rfl rfl
    obtain ⟨ρ', X, hp, hx, hX, -⟩ := hrun ρ
    refine ⟨ρ', _, hp, fun w => rfl, ?_⟩
    rw [hx]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega

end Const

end Backend.Proof
