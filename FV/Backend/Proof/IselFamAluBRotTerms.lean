import FV.Backend.Proof.IselFamAluBShift

/-!
# Family B: rotate helpers (`small_rotr`, `small_rotr_imm`, `a64_rotr`, `a64_rotr_imm`)

Inverse contracts of the one-rule wrappers (`sub`, `sub_imm`, `lsr`, `lsl`, `orr`, `lsr_imm`,
`lsl_imm`, `a64_rotr`, `a64_rotr_imm`: one emitted instruction each), the extern constructors
(`rotr_mask`, `rotr_opposite_amount`, `negate_imm_shift`, `u8_into_imm12`), and the meaning of
the rotate helpers as pure runs (`RotSmall`, `RotWide`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

include hp hc in
theorem alu_rr_imm12_ok {n : Nat} (hn : 40 ≤ n) {op a b : V} {t : CTy}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 376 [op, .ty t, a, b] s v s') :
    ∃ ks, OSz t ks ∧ EmitOut s.1 s'.1 v (fun rd => .data 58 4 [op, .data 93 ks [], .reg rd, a, b]) := by
  have hp' := hp
  isel_split hp hc h 376
  isel_inv [*, rule_inst_2648] at hm he
  rename_i hsz
  obtain ⟨hs, hk⟩ := operand_size_ok hp' hc (by omega) hsz
  rcases hk with ⟨hb, rfl⟩ | ⟨hb, hb', rfl⟩
  · exact ⟨0, .inl ⟨hb, rfl⟩, rfl, _, ‹_›, by rw [hs]⟩
  · exact ⟨1, .inr ⟨hb, hb', rfl⟩, rfl, _, ‹_›, by rw [hs]⟩

include hp hc in
theorem sub_fb_ok {n : Nat} (hn : 50 ≤ n) {a b : V} {t : CTy} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 437 [.ty t, a, b] s v s') :
    ∃ ks, OSz t ks ∧
      EmitOut s.1 s'.1 v (fun rd => .data 58 2 [.data 59 1 [], .data 93 ks [], .reg rd, a, b]) := by
  have hp' := hp
  isel_split hp hc h 437
  isel_inv [*, rule_inst_3138] at hm he
  rename_i hl
  exact alu_rrr_ok hp' hc (by omega) hl

include hp hc in
theorem sub_imm_fb_ok {n : Nat} (hn : 50 ≤ n) {a b : V} {t : CTy} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 438 [.ty t, a, b] s v s') :
    ∃ ks, OSz t ks ∧
      EmitOut s.1 s'.1 v (fun rd => .data 58 4 [.data 59 1 [], .data 93 ks [], .reg rd, a, b]) := by
  have hp' := hp
  isel_split hp hc h 438
  isel_inv [*, rule_inst_3142] at hm he
  rename_i hl
  exact alu_rr_imm12_ok hp' hc (by omega) hl

include hp hc in
theorem lsr_fb_ok {n : Nat} (hn : 50 ≤ n) {a b : V} {t : CTy} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 488 [.ty t, a, b] s v s') :
    ∃ ks, OSz t ks ∧
      EmitOut s.1 s'.1 v (fun rd => .data 58 2 [.data 59 16 [], .data 93 ks [], .reg rd, a, b]) := by
  have hp' := hp
  isel_split hp hc h 488
  isel_inv [*, rule_inst_3371] at hm he
  rename_i hl
  exact alu_rrr_ok hp' hc (by omega) hl

include hp hc in
theorem lsr_imm_fb_ok {n : Nat} (hn : 50 ≤ n) {a b : V} {t : CTy} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 489 [.ty t, a, b] s v s') :
    ∃ ks, OSz t ks ∧
      EmitOut s.1 s'.1 v (fun rd => .data 58 6 [.data 59 16 [], .data 93 ks [], .reg rd, a, b]) := by
  have hp' := hp
  isel_split hp hc h 489
  isel_inv [*, rule_inst_3375] at hm he
  rename_i hl
  exact alu_rr_imm_shift_ok hp' hc (by omega) hl

include hp hc in
theorem lsl_fb_ok {n : Nat} (hn : 50 ≤ n) {a b : V} {t : CTy} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 490 [.ty t, a, b] s v s') :
    ∃ ks, OSz t ks ∧
      EmitOut s.1 s'.1 v (fun rd => .data 58 2 [.data 59 18 [], .data 93 ks [], .reg rd, a, b]) := by
  have hp' := hp
  isel_split hp hc h 490
  isel_inv [*, rule_inst_3380] at hm he
  rename_i hl
  exact alu_rrr_ok hp' hc (by omega) hl

include hp hc in
theorem lsl_imm_fb_ok {n : Nat} (hn : 50 ≤ n) {a b : V} {t : CTy} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 491 [.ty t, a, b] s v s') :
    ∃ ks, OSz t ks ∧
      EmitOut s.1 s'.1 v (fun rd => .data 58 6 [.data 59 18 [], .data 93 ks [], .reg rd, a, b]) := by
  have hp' := hp
  isel_split hp hc h 491
  isel_inv [*, rule_inst_3384] at hm he
  rename_i hl
  exact alu_rr_imm_shift_ok hp' hc (by omega) hl

include hp hc in
theorem orr_fb_ok {n : Nat} (hn : 50 ≤ n) {a b : V} {t : CTy} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 497 [.ty t, a, b] s v s') :
    ∃ ks, OSz t ks ∧
      EmitOut s.1 s'.1 v (fun rd => .data 58 2 [.data 59 2 [], .data 93 ks [], .reg rd, a, b]) := by
  have hp' := hp
  isel_split hp hc h 497
  isel_inv [*, rule_inst_3412] at hm he
  rename_i hl
  exact alu_rrr_ok hp' hc (by omega) hl

include hp hc in
theorem a64_rotr_ok {n : Nat} (hn : 50 ≤ n) {a b : V} {t : CTy} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 513 [.ty t, a, b] s v s') :
    ∃ ks, OSz t ks ∧
      EmitOut s.1 s'.1 v (fun rd => .data 58 2 [.data 59 15 [], .data 93 ks [], .reg rd, a, b]) := by
  have hp' := hp
  isel_split hp hc h 513
  isel_inv [*, rule_inst_3478] at hm he
  rename_i hl
  exact alu_rrr_ok hp' hc (by omega) hl

include hp hc in
theorem a64_rotr_imm_ok {n : Nat} (hn : 50 ≤ n) {a b : V} {t : CTy} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 514 [.ty t, a, b] s v s') :
    ∃ ks, OSz t ks ∧
      EmitOut s.1 s'.1 v (fun rd => .data 58 6 [.data 59 15 [], .data 93 ks [], .reg rd, a, b]) := by
  have hp' := hp
  isel_split hp hc h 514
  isel_inv [*, rule_inst_3482] at hm he
  rename_i hl
  exact alu_rr_imm_shift_ok hp' hc (by omega) hl

/-! ## Extern constructors -/

section Ctor
variable (ctx : Ctx) (st : LState)

theorem ctor_rotr_mask_i8_iff (v : V) (st' : LState) :
    externCtor ctx T.rotr_mask [.ty (.int 8)] st = .ok (v, st') ↔
      v = .op (.immLogic ⟨7, .size32⟩) ∧ st' = st := by
  have : externCtor ctx T.rotr_mask [.ty (.int 8)] st = .ok (.op (.immLogic ⟨7, .size32⟩), st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_rotr_mask_i16_iff (v : V) (st' : LState) :
    externCtor ctx T.rotr_mask [.ty (.int 16)] st = .ok (v, st') ↔
      v = .op (.immLogic ⟨15, .size32⟩) ∧ st' = st := by
  have : externCtor ctx T.rotr_mask [.ty (.int 16)] st =
    .ok (.op (.immLogic ⟨15, .size32⟩), st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_u8_into_imm12_8_iff (v : V) (st' : LState) :
    externCtor ctx T.u8_into_imm12 [.int ((8 : Nat) : Int)] st = .ok (v, st') ↔
      v = .op (.imm12 ⟨8, false⟩) ∧ st' = st := by
  have : externCtor ctx T.u8_into_imm12 [.int ((8 : Nat) : Int)] st = .ok (.op (.imm12 ⟨8, false⟩), st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_u8_into_imm12_16_iff (v : V) (st' : LState) :
    externCtor ctx T.u8_into_imm12 [.int ((16 : Nat) : Int)] st = .ok (v, st') ↔
      v = .op (.imm12 ⟨16, false⟩) ∧ st' = st := by
  have : externCtor ctx T.u8_into_imm12 [.int ((16 : Nat) : Int)] st = .ok (.op (.imm12 ⟨16, false⟩), st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_negate_imm_shift_iff (w s : Nat) (v : V) (st' : LState) :
    externCtor ctx T.negate_imm_shift [.ty (.int w), .op (.immShift s)] st = .ok (v, st') ↔
      v = .op (.immShift (Nat.land ((w + 256 - s) % 256) (w - 1))) ∧ st' = st := by
  have : externCtor ctx T.negate_imm_shift [.ty (.int w), .op (.immShift s)] st =
    .ok (.op (.immShift (Nat.land (((CTy.int w).bits + 256 - s) % 256) ((CTy.int w).bits - 1))), st) :=
    rfl
  rw [this]; simp only [CTy.bits]; simp [eq_comm]

theorem ctor_rotr_opposite_iff (w s : Nat) (v : V) (st' : LState) :
    externCtor ctx T.rotr_opposite_amount [.ty (.int w), .op (.immShift s)] st = .ok (v, st') ↔
      w - Nat.land s (w - 1) < 64 ∧ v = .op (.immShift (w - Nat.land s (w - 1))) ∧ st' = st := by
  have : externCtor ctx T.rotr_opposite_amount [.ty (.int w), .op (.immShift s)] st =
    if (CTy.int w).bits - Nat.land s ((CTy.int w).bits - 1) < 64 then
      .ok (.op (.immShift ((CTy.int w).bits - Nat.land s ((CTy.int w).bits - 1))), st) else .fail := rfl
  rw [this]
  simp only [CTy.bits]
  by_cases hl : w - (s &&& (w - 1)) < 64
  · simp only [Nat.land_eq, hl, ↓reduceIte, ExtResult.ok.injEq, Prod.mk.injEq, true_and]
    constructor <;> rintro ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl⟩
  · simp [hl]

end Ctor

/-- `isel_inv` with the rotate extern lemmas at every round. -/
syntax "fbrot_inv" ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? " at " (ppSpace colGt ident)+ : tactic
macro_rules
  | `(tactic| fbrot_inv [$ts,*] at $hs*) => `(tactic| (
      isel_inv [$ts,*, ctor_put_in_regs_iff, ctor_imm_shift_iff, ctor_rotr_mask_i8_iff, ctor_rotr_mask_i16_iff, ctor_u8_into_imm12_8_iff, ctor_u8_into_imm12_16_iff, ctor_negate_imm_shift_iff, ctor_rotr_opposite_iff, CTy.bits, Int.toNat_zero] at $hs* <;>
      repeat (isel_inv_simp [ctor_put_in_regs_iff, ctor_imm_shift_iff, ctor_rotr_mask_i8_iff, ctor_rotr_mask_i16_iff, ctor_u8_into_imm12_8_iff, ctor_u8_into_imm12_16_iff, ctor_negate_imm_shift_iff, ctor_rotr_opposite_iff, CTy.bits, Int.toNat_zero] at * <;> isel_destruct <;> subst_vars)))

/-! ## Arithmetic of rotations -/

theorem rotr_neg {n : Nat} (hn : 0 < n) (x : BitVec n) (s k : Nat) (hk : k % n = (n - s % n) % n) :
    x.rotateRight k = x.rotateLeft s := by
  rw [BitVec.rotateRight_def, BitVec.rotateLeft_def, hk]
  by_cases h0 : s % n = 0
  · rw [h0, Nat.sub_zero, Nat.mod_self, Nat.sub_zero]
    simp [BitVec.shiftLeft_eq_zero, BitVec.ushiftRight_eq_zero]
  · have h1 : (n - s % n) % n = n - s % n := Nat.mod_eq_of_lt (by omega)
    rw [h1, show n - (n - s % n) = s % n by have := Nat.mod_lt s hn; omega, BitVec.or_comm]

theorem rotr_or {w : Nat} (u : BitVec w) {M : Nat} (hM : M < w) :
    (u <<< (w - M) ||| u >>> M) = u.rotateRight M := by
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt hM, BitVec.or_comm]

theorem neg_toNat {N : Nat} (b : BitVec N) : (0 - b).toNat = (2 ^ N - b.toNat) % 2 ^ N := by
  rw [BitVec.toNat_sub]; simp

theorem neg_mod {N w : Nat} (hNw : (N = 32 ∧ (w = 8 ∨ w = 16 ∨ w = 32)) ∨ (N = 64 ∧ w = 64))
    (b : BitVec N) : (0 - b).toNat % w = (w - b.toNat % w) % w := by
  rw [neg_toNat]
  have hb := b.isLt
  rcases hNw with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [Nat.reducePow] at hb ⊢ <;> omega

/-! ## Instruction semantics -/

theorem ispec_sub_xzr_fb {d : Nat} {rm : Reg} {b : CV} {w : Arm.ArmState} :
    ispec (.aluRRR .sub .size32 (.vreg d .int) .xzr rm) [b] w =
      some ([resX .size32 (0 - opnd .size32 b)], w, .next) := rfl

theorem ispec_sub_xzr64_fb {d : Nat} {rm : Reg} {b : CV} {w : Arm.ArmState} :
    ispec (.aluRRR .sub .size64 (.vreg d .int) .xzr rm) [b] w =
      some ([resX .size64 (0 - opnd .size64 b)], w, .next) := rfl

theorem ispec_sub_imm_fb {sz : OperandSize} {d : Nat} {rn : Reg} {i : Imm12} {a : CV}
    {w : Arm.ArmState} (h : i.bits < 4096) :
    ispec (.aluRRImm12 .sub sz (.vreg d .int) rn i) [a] w =
      some ([resX sz (opnd sz a - BitVec.ofNat _ i.value)], w, .next) := by
  simp only [ispec, h, ↓reduceIte]; rfl

theorem ispec_orr_fb {sz : OperandSize} {d : Nat} {rn rm : Reg} {a b : CV} {w : Arm.ArmState} :
    ispec (.aluRRR .orr sz (.vreg d .int) rn rm) [a, b] w =
      some ([resX sz (opnd sz a ||| opnd sz b)], w, .next) := ispec_aluRRR rfl

theorem ispec_rrr_extr_fb {sz : OperandSize} {d : Nat} {rn rm : Reg} {a b : CV}
    {w : Arm.ArmState} :
    ispec (.aluRRR .extr sz (.vreg d .int) rn rm) [a, b] w =
      some ([resX sz ((opnd sz a).rotateRight ((opnd sz b).toNat % sz.bits))], w, .next) := by
  cases sz <;> rfl

theorem ispec_imm_extr_fb {sz : OperandSize} {d : Nat} {rn : Reg} {L : Nat} (hL : L < sz.bits)
    {a : CV} {w : Arm.ArmState} :
    ispec (.aluRRImmShift .extr sz (.vreg d .int) rn L) [a] w =
      some ([resX sz ((opnd sz a).rotateRight L)], w, .next) := by
  simp only [ispec, hL, ↓reduceIte, shiftVal, Option.map_some]; rfl

theorem codeShapeU_of {st st' : LState} {ms : List MInst} {d k : Nat} {xs : List Nat}
    (hem : st'.emitted = st.emitted ++ ms.toArray) (hnx : st'.nextVreg = st.nextVreg + k)
    (hd : st.nextVreg ≤ d)
    (hdefs : ∀ mi ∈ ms, ∀ e ∈ vdefs mi, st.nextVreg ≤ e ∧ e < st.nextVreg + k)
    (huses : ∀ mi ∈ ms, ∀ u ∈ vuseNums mi, st.nextVreg ≤ u ∨ u ∈ xs) :
    CodeShapeU st st' ms d xs := ⟨hem, by omega, hd, by rw [hnx]; exact hdefs, huses⟩

set_option hygiene false in
/-- Discharge `∀ mi ∈ ms, ∀ u ∈ vuseNums mi, N ≤ u ∨ u ∈ xs` (or `vdefs`) for concrete code. -/
macro "code_facts_fb" : tactic => `(tactic| (
  intro mi hmi e he
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
  rcases hmi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (
    simp only [vdd_aluRRR, vdu_aluRRR, vdd_aluRRR_xzr, vdu_aluRRR_xzr, vdd_aluRRImm12,
      vdu_aluRRImm12, vdd_aluRRImmLogic, vdu_aluRRImmLogic, vdd_aluRRImmShift, vdu_aluRRImmShift,
      List.mem_cons, List.mem_nil_iff, or_false] at he ⊢
    omega)))

section Sem
variable {F : BitVec 64 → Prop} {isem : Sem}

/-- What `small_rotr ty val amt` emitted (`w ∈ {8, 16}`): its result's low `w` bits are the
rotation of `val`'s zero-extended low bits by `amt` modulo `w`. -/
def SmallRot (F : BitVec 64 → Prop) (isem : Sem) (w xv a : Nat) (st st' : LState) (v : V) : Prop :=
  ∃ ms d, v = .reg (.vreg d .int) ∧ CodeShapeU st st' ms d [xv, a] ∧
    ∀ ρ, ∃ ρ', PRun F isem ms ρ ρ' ∧ (∀ z, z < st.nextVreg → ρ' z = ρ z) ∧
      ∀ u : BitVec w, opnd .size32 (ρ xv) = u.setWidth 32 →
        (ρ' d).setWidth w = u.rotateRight ((ρ a).toNat % w)

theorem upd_ne_fb {α : Type} {ρ : Nat → α} {d z : Nat} {x : α} (h : z ≠ d) : upd ρ d x z = ρ z := by
  simp [upd, h]

theorem small_rot_amt {w : Nat} (hw : w = 8 ∨ w = 16) (A : BitVec 32) :
    (A &&& BitVec.ofNat 32 (w - 1)).toNat = A.toNat % w := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show w - 1 < 2 ^ 32 by rcases hw with rfl | rfl <;> decide)]
  exact land_mask_mod (by rcases hw with rfl | rfl <;> simp [IW]) _

theorem small_rot_neg {w : Nat} (hw : w = 8 ∨ w = 16) (B : BitVec 32) (hB : B.toNat < w) :
    (0 - (B - BitVec.ofNat 32 w)).toNat = w - B.toNat := by
  have e : 0 - (B - BitVec.ofNat 32 w) = BitVec.ofNat 32 w - B := by bv_decide
  rw [e, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rcases hw with rfl | rfl <;> simp <;> omega

theorem small_rot_fin {w : Nat} (hw : w = 8 ∨ w = 16) (u : BitVec w) {M : Nat} (hM : M < w) :
    ((u.setWidth 32 <<< (w - M)) ||| (u.setWidth 32 >>> M)).setWidth w = u.rotateRight M := by
  have hw32 : w ≤ 32 := by omega
  rw [BitVec.setWidth_or, shl_setWidth hw32, lsr_zext hw32,
    BitVec.setWidth_setWidth_of_le _ hw32, BitVec.setWidth_eq, rotr_or u hM]

theorem setWidth_resX32 {w : Nat} (hw : w ≤ 32) (r : BitVec OperandSize.size32.bits) :
    (resX .size32 r).setWidth w = r.setWidth w := by
  simp only [resX, ofX, BitVec.setWidth_setWidth_of_le _ (show w ≤ 128 by omega)]
  exact BitVec.setWidth_setWidth_of_le r (by omega)

theorem small_rotr_run (hR : Refines F isem) {w : Nat} (hw : w = 8 ∨ w = 16) {imm : Imm12}
    (himm : imm.value = w) (hib : imm.bits < 4096) {xv a : Nat} {st st' : LState}
    (hxv : xv < st.nextVreg) (ha : a < st.nextVreg)
    (hem : st'.emitted = st.emitted ++
      [MInst.aluRRImmLogic .and .size32 (.vreg st.nextVreg .int) (.vreg a .int) ⟨w - 1, .size32⟩,
       .aluRRImm12 .sub .size32 (.vreg (st.nextVreg + 1) .int) (.vreg st.nextVreg .int) imm,
       .aluRRR .sub .size32 (.vreg (st.nextVreg + 2) .int) .xzr (.vreg (st.nextVreg + 1) .int),
       .aluRRR .lsr .size32 (.vreg (st.nextVreg + 3) .int) (.vreg xv .int) (.vreg st.nextVreg .int),
       .aluRRR .lsl .size32 (.vreg (st.nextVreg + 4) .int) (.vreg xv .int)
         (.vreg (st.nextVreg + 2) .int),
       .aluRRR .orr .size32 (.vreg (st.nextVreg + 5) .int) (.vreg (st.nextVreg + 4) .int)
         (.vreg (st.nextVreg + 3) .int)].toArray)
    (hnx : st'.nextVreg = st.nextVreg + 6) :
    SmallRot F isem w xv a st st' (.reg (.vreg (st.nextVreg + 5) .int)) := by
  have hW : IW w := by rcases hw with rfl | rfl <;> simp [IW]
  have hi : ImmLogic.ofNat? (w - 1) .size32 = some ⟨w - 1, .size32⟩ := by
    rcases hw with rfl | rfl <;> rfl
  refine ⟨_, _, rfl, codeShapeU_of hem hnx (by omega) (by code_facts_fb) (by code_facts_fb),
    fun ρ => ⟨_, prun_rr hR rfl (fun w => ispec_and_imm_fb hi)
      (prun_rr hR rfl (fun w => ispec_sub_imm_fb hib)
      (prun_rr hR rfl (fun w => ispec_sub_xzr_fb)
      (prun_rrr hR (operands_aluRRR _ _ _ _ _) (fun w => ispec_rrr_shift_fb (.inr (.inl rfl)))
      (prun_rrr hR (operands_aluRRR _ _ _ _ _) (fun w => ispec_rrr_shift_fb (.inl rfl))
      (prun_rrr hR (operands_aluRRR _ _ _ _ _) (fun w => ispec_orr_fb) (prun_nil _)))))), ?_, ?_⟩⟩
  · intro z hz
    have h0 : z ≠ st.nextVreg := by omega
    have h1 : z ≠ st.nextVreg + 1 := by omega
    have h2 : z ≠ st.nextVreg + 2 := by omega
    have h3 : z ≠ st.nextVreg + 3 := by omega
    have h4 : z ≠ st.nextVreg + 4 := by omega
    have h5 : z ≠ st.nextVreg + 5 := by omega
    simp only [upd, h0, h1, h2, h3, h4, h5, ↓reduceIte]
  · intro u hu
    have hMlt : (ρ a).toNat % w < w := Nat.mod_lt _ hW.pos
    simp (disch := omega) only [upd_ne_fb, upd_same, opnd_resX, shiftF, hu]
    rw [setWidth_resX32 (by omega)]
    have hA := (small_rot_amt hw (opnd .size32 (ρ a))).trans (opnd_mod hW .size32 (ρ a))
    generalize opnd .size32 (ρ a) = A at hA ⊢
    revert A
    show ∀ A : BitVec 32, (A &&& BitVec.ofNat 32 (w - 1)).toNat = (ρ a).toNat % w →
      BitVec.setWidth w (BitVec.setWidth 32 u <<<
        ((0 - ((A &&& BitVec.ofNat 32 (w - 1)) - BitVec.ofNat 32 imm.value)).toNat % 32) |||
        BitVec.setWidth 32 u >>> ((A &&& BitVec.ofNat 32 (w - 1)).toNat % 32)) =
      u.rotateRight ((ρ a).toNat % w)
    intro A hA
    have hN := small_rot_neg hw _ (by rw [hA]; exact hMlt)
    rw [himm, hN, hA, Nat.mod_eq_of_lt (show w - (ρ a).toNat % w < 32 by omega),
      Nat.mod_eq_of_lt (show (ρ a).toNat % w < 32 by omega)]
    exact small_rot_fin hw u hMlt

/-- What `small_rotr_imm ty val n` emitted (`w ∈ {8, 16}`, `n < w`). -/
def SmallRotImm (F : BitVec 64 → Prop) (isem : Sem) (w xv n : Nat) (st st' : LState) (v : V) :
    Prop :=
  ∃ ms d, v = .reg (.vreg d .int) ∧ CodeShapeU st st' ms d [xv] ∧
    ∀ ρ, ∃ ρ', PRun F isem ms ρ ρ' ∧ (∀ z, z < st.nextVreg → ρ' z = ρ z) ∧
      ∀ u : BitVec w, opnd .size32 (ρ xv) = u.setWidth 32 → (ρ' d).setWidth w = u.rotateRight n

theorem small_rotr_imm_run (hR : Refines F isem) {w : Nat} (hw : w = 8 ∨ w = 16) {n : Nat}
    (hn : n < w) {xv : Nat} {st st' : LState} (hxv : xv < st.nextVreg)
    (hem : st'.emitted = st.emitted ++
      [MInst.aluRRImmShift .lsr .size32 (.vreg st.nextVreg .int) (.vreg xv .int) n,
       .aluRRImmShift .lsl .size32 (.vreg (st.nextVreg + 1) .int) (.vreg xv .int)
         (w - Nat.land n (w - 1)),
       .aluRRR .orr .size32 (.vreg (st.nextVreg + 2) .int) (.vreg (st.nextVreg + 1) .int)
         (.vreg st.nextVreg .int)].toArray)
    (hnx : st'.nextVreg = st.nextVreg + 3) :
    SmallRotImm F isem w xv n st st' (.reg (.vreg (st.nextVreg + 2) .int)) := by
  have hW : IW w := by rcases hw with rfl | rfl <;> simp [IW]
  have hL : Nat.land n (w - 1) = n := by rw [land_mask_mod hW, Nat.mod_eq_of_lt hn]
  rw [hL] at hem
  refine ⟨_, _, rfl, codeShapeU_of hem hnx (by omega) (by code_facts_fb) (by code_facts_fb),
    fun ρ => ⟨_, prun_rr hR rfl (fun _ => ispec_imm_shift_fb (.inr (.inl rfl))
        (show n < OperandSize.size32.bits by simp [OperandSize.bits]; omega))
      (prun_rr hR rfl (fun _ => ispec_imm_shift_fb (.inl rfl)
        (show w - n < OperandSize.size32.bits by simp [OperandSize.bits]; omega))
      (prun_rrr hR (operands_aluRRR _ _ _ _ _) (fun _ => ispec_orr_fb) (prun_nil _))), ?_, ?_⟩⟩
  · intro z hz
    have h0 : z ≠ st.nextVreg := by omega
    have h1 : z ≠ st.nextVreg + 1 := by omega
    have h2 : z ≠ st.nextVreg + 2 := by omega
    simp only [upd, h0, h1, h2, ↓reduceIte]
  · intro u hu
    simp (disch := omega) only [upd_ne_fb, upd_same, opnd_resX, shiftF, hu]
    rw [setWidth_resX32 (by omega)]
    exact small_rot_fin hw u hn

set_option maxHeartbeats 1000000 in
include hp hc in
/-- **Contract of `small_rotr`** (`lower.isle:1879`) at `i8`/`i16`. -/
theorem small_rotr_ok (hR : Refines F isem) {n : Nat} (hn : 100 ≤ n) {w : Nat} (hw : w = 8 ∨ w = 16)
    {xv a : Nat} {s s' : LState × Array RuleId} {v : V} (hxv : xv < s.1.nextVreg)
    (ha : a < s.1.nextVreg)
    (h : ApplyInternal p (sem ctx) cfg n 27 710
      [.ty (.int w), .reg (.vreg xv .int), .reg (.vreg a .int)] s v s') :
    SmallRot F isem w xv a s.1 s'.1 v := by
  have hp' := hp
  isel_split hp hc h 710
  all_goals fbrot_inv [*, rule_lower_1879] at hm he
  all_goals
    have hA1 := ‹ApplyInternal _ _ _ _ 27 502 _ _ _ _›
    have hA2 := ‹ApplyInternal _ _ _ _ 27 438 _ _ _ _›
    have hA3 := ‹ApplyInternal _ _ _ _ 27 437 _ _ _ _›
    have hA4 := ‹ApplyInternal _ _ _ _ 27 488 _ _ _ _›
    have hA5 := ‹ApplyInternal _ _ _ _ 27 490 _ _ _ _›
    have hA6 := ‹ApplyInternal _ _ _ _ 27 497 _ _ _ _›
    have h32 : IW 32 := by simp [IW]
    obtain ⟨k1, hk1, rfl, m1, hm1, hs1⟩ := and_imm_ok hp' hc (by omega) hA1
    dsimp only at hm1 hs1
    rw [ofV_aluRRImmLogic_fb _ _ (rfl : ALUOp.ofIdx? 4 = some .and) (hk1.ofIdx h32)] at hm1
    cases hm1
    obtain ⟨k2, hk2, rfl, m2, hm2, hs2⟩ := sub_imm_fb_ok hp' hc (by omega) hA2
    dsimp only at hm2 hs2
    rw [ofV_aluRRImm12_fb _ _ (rfl : ALUOp.ofIdx? 1 = some .sub) (hk2.ofIdx h32)] at hm2
    cases hm2
    obtain ⟨k3, hk3, rfl, m3, hm3, hs3⟩ := sub_fb_ok hp' hc (by omega) hA3
    dsimp only at hm3 hs3
    rw [ofV_aluRRR (rfl : ALUOp.ofIdx? 1 = some .sub) (hk3.ofIdx h32)] at hm3
    cases hm3
    obtain ⟨k4, hk4, rfl, m4, hm4, hs4⟩ := lsr_fb_ok hp' hc (by omega) hA4
    dsimp only at hm4 hs4
    rw [ofV_aluRRR (rfl : ALUOp.ofIdx? 16 = some .lsr) (hk4.ofIdx h32)] at hm4
    cases hm4
    obtain ⟨k5, hk5, rfl, m5, hm5, hs5⟩ := lsl_fb_ok hp' hc (by omega) hA5
    dsimp only at hm5 hs5
    rw [ofV_aluRRR (rfl : ALUOp.ofIdx? 18 = some .lsl) (hk5.ofIdx h32)] at hm5
    cases hm5
    obtain ⟨k6, hk6, rfl, m6, hm6, hs6⟩ := orr_fb_ok hp' hc (by omega) hA6
    dsimp only at hm6 hs6
    rw [ofV_aluRRR (rfl : ALUOp.ofIdx? 2 = some .orr) (hk6.ofIdx h32)] at hm6
    cases hm6
    subst hs6
    simp only [hs1, hs2, hs3, hs4, hs5]
    refine small_rotr_run hR (by first | exact .inl rfl | exact .inr rfl) (imm := ⟨_, false⟩) rfl
      (by decide) hxv ha ?_ rfl
    simp only [LState.emit, LState.fresh, szOf, Nat.add_assoc, Nat.reduceAdd, Nat.reduceLeDiff,
      ↓reduceIte]
    apply Array.ext'
    simp
    all_goals decide

end Sem

end Backend.Proof
