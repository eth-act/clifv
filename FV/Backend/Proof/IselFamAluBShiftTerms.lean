import FV.Backend.Proof.IselTermsShift
import FV.Backend.Proof.IselCmpExt

/-!
# Family B: inverse contracts of the emitting helpers the shift rules call

`alu_rrr`, `alu_rr_imm_shift`, `alu_rr_imm_logic`, `and_imm`, `output_reg`: a successful
internal call (`ApplyInternal`) emitted one instruction (decoded by `MInst.ofV`) into a fresh
vreg, with the operand size of `operand_size` (`OSz`). Proved by inverse evaluation
(`isel_split`, `isel_inv`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- `operand_size t` returned the `OperandSize` index `ks`. -/
def OSz (t : CTy) (ks : Nat) : Prop := (t.bits ≤ 32 ∧ ks = 0) ∨ (32 < t.bits ∧ t.bits ≤ 64 ∧ ks = 1)

variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

/-- The shape of an emitting helper's result: a fresh vreg `v`, one instruction `m` decoded from
`iv` (with the fresh register as destination), appended. -/
def EmitOut (s s' : LState) (v : V) (iv : Reg → V) : Prop :=
  v = .reg (s.fresh .int).1 ∧ ∃ m, MInst.ofV (iv (s.fresh .int).1) = some m ∧
    s' = (s.fresh .int).2.emit m

include hp hc in
theorem alu_rrr_ok {n : Nat} (hn : 40 ≤ n) {op a b : V} {t : CTy} {s s' : LState × Array RuleId}
    {v : V} (h : ApplyInternal p (sem ctx) cfg n 27 362 [op, .ty t, a, b] s v s') :
    ∃ ks, OSz t ks ∧ EmitOut s.1 s'.1 v (fun rd => .data 58 2 [op, .data 93 ks [], .reg rd, a, b]) := by
  have hp' := hp
  isel_split hp hc h 362
  isel_inv [*, rule_inst_2545] at hm he
  rename_i hsz
  obtain ⟨hs, hk⟩ := operand_size_ok hp' hc (by omega) hsz
  rcases hk with ⟨hb, rfl⟩ | ⟨hb, hb', rfl⟩
  · exact ⟨0, .inl ⟨hb, rfl⟩, rfl, _, ‹_›, by rw [hs]⟩
  · exact ⟨1, .inr ⟨hb, hb', rfl⟩, rfl, _, ‹_›, by rw [hs]⟩

include hp hc in
theorem alu_rr_imm_shift_ok {n : Nat} (hn : 40 ≤ n) {op a b : V} {t : CTy}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 361 [op, .ty t, a, b] s v s') :
    ∃ ks, OSz t ks ∧ EmitOut s.1 s'.1 v (fun rd => .data 58 6 [op, .data 93 ks [], .reg rd, a, b]) := by
  have hp' := hp
  isel_split hp hc h 361
  isel_inv [*, rule_inst_2537] at hm he
  rename_i hsz
  obtain ⟨hs, hk⟩ := operand_size_ok hp' hc (by omega) hsz
  rcases hk with ⟨hb, rfl⟩ | ⟨hb, hb', rfl⟩
  · exact ⟨0, .inl ⟨hb, rfl⟩, rfl, _, ‹_›, by rw [hs]⟩
  · exact ⟨1, .inr ⟨hb, hb', rfl⟩, rfl, _, ‹_›, by rw [hs]⟩

include hp hc in
theorem alu_rr_imm_logic_ok {n : Nat} (hn : 40 ≤ n) {op a b : V} {t : CTy}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 360 [op, .ty t, a, b] s v s') :
    ∃ ks, OSz t ks ∧ EmitOut s.1 s'.1 v (fun rd => .data 58 5 [op, .data 93 ks [], .reg rd, a, b]) := by
  have hp' := hp
  isel_split hp hc h 360
  isel_inv [*, rule_inst_2529] at hm he
  rename_i hsz
  obtain ⟨hs, hk⟩ := operand_size_ok hp' hc (by omega) hsz
  rcases hk with ⟨hb, rfl⟩ | ⟨hb, hb', rfl⟩
  · exact ⟨0, .inl ⟨hb, rfl⟩, rfl, _, ‹_›, by rw [hs]⟩
  · exact ⟨1, .inr ⟨hb, hb', rfl⟩, rfl, _, ‹_›, by rw [hs]⟩

include hp hc in
theorem and_imm_ok {n : Nat} (hn : 50 ≤ n) {a b : V} {t : CTy}
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 27 502 [.ty t, a, b] s v s') :
    ∃ ks, OSz t ks ∧
      EmitOut s.1 s'.1 v (fun rd => .data 58 5 [.data 59 4 [], .data 93 ks [], .reg rd, a, b]) := by
  have hp' := hp
  isel_split hp hc h 502
  isel_inv [*, rule_inst_3431] at hm he
  rename_i hl
  exact alu_rr_imm_logic_ok hp' hc (by omega) hl

include hp hc in
theorem output_reg_ok {n : Nat} (hn : 40 ≤ n) {r : Reg} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 25 172 [.reg r] s v s') :
    v = .regsVec [[r]] ∧ s'.1 = s.1 := by
  isel_split hp hc h 172
  isel_inv [*, rule_prelude_lower_105] at hm he

section Ctor
variable (ctx : Ctx) (st : LState)

theorem ctor_put_in_regs_iff (x : Nat) (v : V) (st' : LState) :
    externCtor ctx T.put_in_regs [.value x] st = .ok (v, st') ↔
      ∃ r, ctx.valueReg? x = some r ∧ v = .regs [r] ∧ st' = st := by
  have : externCtor ctx T.put_in_regs [.value x] st = match ctx.valueReg? x with
      | some r => .ok (.regs [r], st)
      | none => .unmodeled s!"put_in_regs v{x}" := rfl
  rw [this]
  cases ctx.valueReg? x <;> simp [eq_comm]

theorem ctor_imm_shift_iff (w : Nat) (c : Int) (v : V) (st' : LState) :
    externCtor ctx T.imm_shift_from_imm64 [.ty (.int w), .int c] st = .ok (v, st') ↔
      Nat.land (u64 c) (w - 1) < 64 ∧ v = .op (.immShift (Nat.land (u64 c) (w - 1))) ∧ st' = st := by
  have : externCtor ctx T.imm_shift_from_imm64 [.ty (.int w), .int c] st =
    if Nat.land (u64 c) ((CTy.int w).bits - 1) < 64 then
      .ok (.op (.immShift (Nat.land (u64 c) ((CTy.int w).bits - 1))), st) else .fail := rfl
  rw [this]
  simp only [CTy.bits]
  by_cases hl : u64 c &&& (w - 1) < 64
  · simp only [Nat.land_eq, hl, ↓reduceIte, ExtResult.ok.injEq, Prod.mk.injEq, true_and]
    constructor <;> rintro ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl⟩
  · simp [hl]

theorem ctor_shift_mask_i8_iff (v : V) (st' : LState) :
    externCtor ctx T.shift_mask [.ty (.int 8)] st = .ok (v, st') ↔
      v = .op (.immLogic ⟨7, .size32⟩) ∧ st' = st := by
  rw [ctor_shift_mask_i8]; simp [eq_comm]

theorem ctor_shift_mask_i16_iff (v : V) (st' : LState) :
    externCtor ctx T.shift_mask [.ty (.int 16)] st = .ok (v, st') ↔
      v = .op (.immLogic ⟨15, .size32⟩) ∧ st' = st := by
  rw [ctor_shift_mask_i16]; simp [eq_comm]

end Ctor

/-- `isel_inv` with this module's extern lemmas at every round. -/
syntax "fb_inv" ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? " at " (ppSpace colGt ident)+ : tactic
macro_rules
  | `(tactic| fb_inv [$ts,*] at $hs*) => `(tactic| (isel_inv [$ts,*, ctor_put_in_regs_iff,
      ctor_imm_shift_iff, ctor_shift_mask_i8_iff, ctor_shift_mask_i16_iff] at $hs* <;>
      repeat (isel_inv_simp [ctor_put_in_regs_iff, ctor_imm_shift_iff, ctor_shift_mask_i8_iff,
        ctor_shift_mask_i16_iff] at * <;> isel_destruct <;> subst_vars)))

/-! ## Arithmetic of the shift amount -/

theorem toNat_setWidth_mod {m : Nat} (a : BitVec m) (n w : Nat) (h : w ∣ 2 ^ n) :
    (a.setWidth n).toNat % w = a.toNat % w := by
  rw [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ h]

/-- The integer widths `i8..i64`. -/
def IW (w : Nat) : Prop := w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64

theorem IW.dvd {w n : Nat} (hw : IW w) (hn : 6 ≤ n) : w ∣ 2 ^ n := by
  have : w ∣ 2 ^ 6 := by rcases hw with rfl | rfl | rfl | rfl <;> decide
  exact Nat.dvd_trans this (Nat.pow_dvd_pow 2 hn)

theorem IW.le {w : Nat} (hw : IW w) : w ≤ 64 := by rcases hw with rfl | rfl | rfl | rfl <;> decide

theorem opnd_mod {w : Nat} (hw : IW w) (sz : OperandSize) (a : CV) :
    (opnd sz a).toNat % w = a.toNat % w := by
  have h1 : 6 ≤ sz.bits := by cases sz <;> decide
  simp only [opnd, lo64]
  rw [toNat_setWidth_mod _ _ _ (hw.dvd h1), toNat_setWidth_mod _ _ _ (hw.dvd (by decide))]

theorem amt_of_holds {w : Nat} (hw : IW w) {yv : Clif.Val} {x : CV} (h : VHolds yv x) :
    yv.bits.toNat % w = x.toNat % w := by
  obtain ⟨ty, b⟩ := yv
  simp only [VHolds] at h
  subst h
  have : 6 ≤ ty.width := by cases ty <;> decide
  exact toNat_setWidth_mod _ _ _ (hw.dvd this)

theorem opnd_resX (sz : OperandSize) (r : BitVec sz.bits) : opnd sz (resX sz r) = r := by
  simp only [opnd, resX, ofX, lo64, BitVec.setWidth_setWidth_of_le _ (show 64 ≤ 128 by decide),
    BitVec.setWidth_eq, BitVec.setWidth_setWidth_of_le _ (opSize_bits_le sz)]

theorem land_mask_mod {w : Nat} (hw : IW w) (c : Nat) : Nat.land c (w - 1) = c % w := by
  change c &&& (w - 1) = c % w
  rcases hw with rfl | rfl | rfl | rfl
  · exact Nat.and_two_pow_sub_one_eq_mod c 3
  · exact Nat.and_two_pow_sub_one_eq_mod c 4
  · exact Nat.and_two_pow_sub_one_eq_mod c 5
  · exact Nat.and_two_pow_sub_one_eq_mod c 6

theorem u64_imm64OfIconst_fb {ty : Clif.Ty} (hw : ty.width ≤ 64) (c : BitVec ty.width) :
    u64 (imm64OfIconst ty c) = c.toNat := by
  unfold imm64OfIconst
  have hlt := c.isLt
  split
  · have : c.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hw)
    unfold u64; omega
  · have h64 : ty.width = 64 := by omega
    unfold u64
    rw [BitVec.toInt_eq_toNat_cond]
    have h2 : (2 : Nat) ^ ty.width = 2 ^ 64 := by rw [h64]
    rw [h2] at hlt ⊢
    split <;> omega

theorem lookup_zip_single_fb {l : List Nat} {a v : Clif.Val} {x : Nat}
    (h : (l.zip [a]).lookup x = some v) : v = a := by
  cases l with
  | nil => simp at h
  | cons z zs =>
    simp only [List.zip_cons_cons, List.zip_nil_right, List.lookup] at h
    split at h
    · exact (Option.some.inj h).symm
    · cases h

/-- The value of a looked-through `iconst` (`DFGCons`). -/
theorem dfg_iconst_fb {fr : Clif.Frame} (hd : DFGCons ctx fr) {y j : Nat} {info : IInfo}
    {ty : Clif.Ty} {imm : BitVec ty.width} {v : Clif.Val} (hj : ctx.defInst? y = some j)
    (hi : ctx.insts[j]? = some info) (hcl : info.clif = some (.iconst ty imm))
    (hv : fr.regs y = some v) : v = ⟨ty, imm⟩ := by
  obtain ⟨vals, hev', hl⟩ := hd.1 y j info _ v hj hi hcl rfl hv
  have := hev' default
  simp only [Clif.evalInst, pure] at this
  cases this
  exact lookup_zip_single_fb hl

/-! ## The emitted instructions' meaning -/

/-- The three shift operations. -/
def IsShift (op : ALUOp) : Prop := op = .lsl ∨ op = .lsr ∨ op = .asr

theorem ShiftOp.isShift {k : Nat} {op : ALUOp} (h : ShiftOp k op) : IsShift op := by
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem ispec_rrr_shift_fb {op : ALUOp} (hop : IsShift op) {sz : OperandSize} {d : Nat}
    {rn rm : Reg} {a b : CV} {w : Arm.ArmState} :
    ispec (.aluRRR op sz (.vreg d .int) rn rm) [a, b] w =
      some ([resX sz (shiftF op (opnd sz a) ((opnd sz b).toNat % sz.bits))], w, .next) := by
  rcases hop with rfl | rfl | rfl <;> cases sz <;> rfl

theorem ispec_imm_shift_fb {op : ALUOp} (hop : IsShift op) {sz : OperandSize} {d : Nat}
    {rn : Reg} {L : Nat} (hL : L < sz.bits) {a : CV} {w : Arm.ArmState} :
    ispec (.aluRRImmShift op sz (.vreg d .int) rn L) [a] w =
      some ([resX sz (shiftF op (opnd sz a) L)], w, .next) := by
  rcases hop with rfl | rfl | rfl <;>
    simp only [ispec, hL, ↓reduceIte, shiftVal, shiftF, Option.map_some] <;> rfl

theorem ispec_and_imm_fb {d : Nat} {rn : Reg} {m : Nat}
    (hi : ImmLogic.ofNat? m .size32 = some ⟨m, .size32⟩) {a : CV} {w : Arm.ArmState} :
    ispec (.aluRRImmLogic .and .size32 (.vreg d .int) rn ⟨m, .size32⟩) [a] w =
      some ([resX .size32 (opnd .size32 a &&& BitVec.ofNat _ m)], w, .next) := by
  simp only [ispec, hi, ne_eq, reduceCtorEq, not_false_eq_true, and_self, ↓reduceIte, aluVal,
    Option.map_some]
  rfl

/-! ## `do_shift`'s result -/

section Sem
variable {F : BitVec 64 → Prop} {isem : Sem}

/-- What `do_shift op ty a y` (value register `xa`, amount value `y`) returned: a fresh vreg `d`
defined by code reading `xa`, `y` and fresh vregs, holding at the operand size of `w` the shift
of `xa` by the amount modulo `w`, in every frame. -/
def ShiftRes (F : BitVec 64 → Prop) (isem : Sem) (ctx : Ctx) (op : ALUOp) (w xa y : Nat)
    (st st' : LState) (v : V) : Prop :=
  ∃ ms d, v = .reg (.vreg d .int) ∧ CodeShapeU st st' ms d [xa, y] ∧
    ∀ (fr : Clif.Frame) (ρ : Nat → CV) (yv : Clif.Val), ValsHeld fr ρ → DFGCons ctx fr →
      fr.regs y = some yv →
      ∃ ρ', PRun F isem ms ρ ρ' ∧
        opnd (szOf w) (ρ' d) = shiftF op (opnd (szOf w) (ρ xa)) (yv.bits.toNat % w)

theorem codeShapeU_one {st : LState} {m : MInst} {xs : List Nat} (hd : vdefs m = [st.nextVreg])
    (hu : ∀ u ∈ vuseNums m, u ∈ xs) :
    CodeShapeU st ((st.fresh .int).2.emit m) [m] st.nextVreg xs := by
  refine ⟨by simp [LState.emit, LState.fresh], by simp [LState.emit, LState.fresh], Nat.le_refl _,
    ?_, ?_⟩
  · intro mi hmi e he
    simp only [List.mem_singleton] at hmi; subst hmi
    rw [hd, List.mem_singleton] at he; subst he
    simp [LState.emit, LState.fresh]
  · intro mi hmi u hu'
    simp only [List.mem_singleton] at hmi; subst hmi
    exact .inr (hu u hu')

theorem codeShapeU_two {st : LState} {m1 m2 : MInst} {xs : List Nat}
    (hd1 : vdefs m1 = [st.nextVreg]) (hd2 : vdefs m2 = [st.nextVreg + 1])
    (hu1 : ∀ u ∈ vuseNums m1, u ∈ xs) (hu2 : ∀ u ∈ vuseNums m2, u = st.nextVreg ∨ u ∈ xs) :
    CodeShapeU st ((((st.fresh .int).2.emit m1).fresh .int).2.emit m2) [m1, m2]
      (st.nextVreg + 1) xs := by
  refine ⟨?_, by simp only [LState.emit, LState.fresh]; omega, by omega, ?_, ?_⟩
  · simp only [LState.emit, LState.fresh]
    apply Array.ext'; simp
  · intro mi hmi e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
    rcases hmi with rfl | rfl
    · rw [hd1, List.mem_singleton] at he; subst he
      simp only [LState.emit, LState.fresh]; omega
    · rw [hd2, List.mem_singleton] at he; subst he
      simp only [LState.emit, LState.fresh]; omega
  · intro mi hmi u hu'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmi
    rcases hmi with rfl | rfl
    · exact .inr (hu1 u hu')
    · rcases hu2 u hu' with h | h
      · exact .inl (by omega)
      · exact .inr h

theorem IW.pos {w : Nat} (hw : IW w) : 0 < w := by rcases hw with rfl | rfl | rfl | rfl <;> decide

/-- Rule 1631: one immediate shift by the looked-through constant masked to the width. -/
theorem shiftRes_imm (hR : Refines F isem) {op : ALUOp} (hop : IsShift op) {w : Nat} (hw : IW w)
    {xa y j : Nat} {info : IInfo} {ty : Clif.Ty} {imm : BitVec ty.width}
    (hj : ctx.defInst? y = some j) (hi : ctx.insts[j]? = some info)
    (hcl : info.clif = some (.iconst ty imm)) (hety : eTy ty = true) (st : LState) :
    ShiftRes F isem ctx op w xa y st
      ((st.fresh .int).2.emit (.aluRRImmShift op (szOf w) (st.fresh .int).1 (.vreg xa .int)
        (Nat.land (u64 (imm64OfIconst ty imm)) (w - 1)))) (.reg (st.fresh .int).1) := by
  have hf : (st.fresh .int).1 = .vreg st.nextVreg .int := rfl
  rw [hf]
  have hL : Nat.land (u64 (imm64OfIconst ty imm)) (w - 1) = imm.toNat % w := by
    rw [land_mask_mod hw, u64_imm64OfIconst_fb (eTy_width hety)]
  have hsz : w ≤ (szOf w).bits := szOf_bits hw.le
  have hLt : Nat.land (u64 (imm64OfIconst ty imm)) (w - 1) < (szOf w).bits := by
    rw [hL]; have := Nat.mod_lt imm.toNat hw.pos; omega
  refine ⟨_, _, rfl, codeShapeU_one rfl (by simp [vdu_aluRRImmShift]), fun fr ρ yv _ hdfg hy => ?_⟩
  have hyv := dfg_iconst_fb hdfg hj hi hcl hy
  subst hyv
  refine ⟨_, prun_rr hR rfl (fun w => ispec_imm_shift_fb hop hLt) (prun_nil _), ?_⟩
  rw [upd_same, opnd_resX, hL]

/-- Rules 1622/1623: one register shift at 32/64 bits (the hardware takes the amount modulo the
width). -/
theorem shiftRes_rrr (hR : Refines F isem) {op : ALUOp} (hop : IsShift op) {w : Nat}
    (hw : w = 32 ∨ w = 64) {xa y : Nat} (st : LState) :
    ShiftRes F isem ctx op w xa y st
      ((st.fresh .int).2.emit (.aluRRR op (szOf w) (st.fresh .int).1 (.vreg xa .int) (.vreg y .int)))
      (.reg (st.fresh .int).1) := by
  have hf : (st.fresh .int).1 = .vreg st.nextVreg .int := rfl
  rw [hf]
  have hW : IW w := by rcases hw with rfl | rfl <;> simp [IW]
  refine ⟨_, _, rfl, codeShapeU_one rfl (by simp [vdu_aluRRR]), fun fr ρ yv hvals _ hy => ?_⟩
  refine ⟨_, prun_rrr hR (operands_aluRRR _ _ _ _ _) (fun w => ispec_rrr_shift_fb hop)
    (prun_nil _), ?_⟩
  have hb : (szOf w).bits = w := by rcases hw with rfl | rfl <;> rfl
  rw [upd_same, opnd_resX]
  congr 1
  rw [amt_of_holds hW (hvals y yv hy), ← opnd_mod hW (szOf w) (ρ y)]
  exact congrArg (fun m => (opnd (szOf w) (ρ y)).toNat % m) hb

/-- Rule 1612 (`i8`/`i16`): mask the amount with `w - 1`, then a 32-bit register shift. -/
theorem shiftRes_mask (hR : Refines F isem) {op : ALUOp} (hop : IsShift op) {w : Nat}
    (hw : w = 8 ∨ w = 16) {xa y : Nat} (st : LState) (hxa : xa < st.nextVreg)
    (hi : ImmLogic.ofNat? (w - 1) .size32 = some ⟨w - 1, .size32⟩) :
    ShiftRes F isem ctx op w xa y st
      ((((st.fresh .int).2.emit (.aluRRImmLogic .and .size32 (st.fresh .int).1 (.vreg y .int)
        ⟨w - 1, .size32⟩)).fresh .int).2.emit
        (.aluRRR op .size32 (((st.fresh .int).2.emit (.aluRRImmLogic .and .size32 (st.fresh .int).1
          (.vreg y .int) ⟨w - 1, .size32⟩)).fresh .int).1 (.vreg xa .int) (st.fresh .int).1))
      (.reg (((st.fresh .int).2.emit (.aluRRImmLogic .and .size32 (st.fresh .int).1
          (.vreg y .int) ⟨w - 1, .size32⟩)).fresh .int).1) := by
  have hf : (st.fresh .int).1 = .vreg st.nextVreg .int := rfl
  have hf2 : (((st.fresh .int).2.emit (.aluRRImmLogic .and .size32 (.vreg st.nextVreg .int)
      (.vreg y .int) ⟨w - 1, .size32⟩)).fresh .int).1 = .vreg (st.nextVreg + 1) .int := rfl
  rw [hf, hf2]
  have hW : IW w := by rcases hw with rfl | rfl <;> simp [IW]
  have hsz : szOf w = .size32 := by rcases hw with rfl | rfl <;> rfl
  refine ⟨_, _, rfl, codeShapeU_two rfl rfl (by simp [vdu_aluRRImmLogic])
    (by simp [vdu_aluRRR]), fun fr ρ yv hvals _ hy => ?_⟩
  refine ⟨_, prun_rr hR rfl (fun w => ispec_and_imm_fb hi) (prun_rrr hR (operands_aluRRR _ _ _ _ _)
    (fun w => ispec_rrr_shift_fb hop) (prun_nil _)), ?_⟩
  have hne : xa ≠ st.nextVreg := by omega
  rw [hsz, upd_same, opnd_resX]
  simp only [upd, hne, ↓reduceIte, opnd_resX]
  congr 1
  have hamt : (opnd .size32 (ρ y) &&& BitVec.ofNat _ (w - 1)).toNat = (opnd .size32 (ρ y)).toNat % w := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show w - 1 < 2 ^ OperandSize.size32.bits by
      rcases hw with rfl | rfl <;> decide)]
    exact land_mask_mod hW _
  rw [hamt, Nat.mod_eq_of_lt (show (opnd .size32 (ρ y)).toNat % w < OperandSize.size32.bits by
      have := Nat.mod_lt (opnd .size32 (ρ y)).toNat hW.pos
      rcases hw with rfl | rfl <;> simp [OperandSize.bits] <;> omega),
    opnd_mod hW, amt_of_holds hW (hvals y yv hy)]

theorem OSz.ofIdx {w ks : Nat} (hw : IW w) (h : OSz (.int w) ks) :
    OperandSize.ofIdx? ks = some (szOf w) := by
  rcases hw with rfl | rfl | rfl | rfl <;>
    rcases h with ⟨h1, rfl⟩ | ⟨h1, -, rfl⟩ <;> first | rfl | (exfalso; simp [CTy.bits] at h1)

set_option maxHeartbeats 1000000 in
include hp hc in
/-- **Contract of `do_shift`** (all four rules). -/
theorem do_shift_ok (hR : Refines F isem) {f : Clif.Function} (hctx : CtxInv f ctx) {n : Nat}
    (hn : 80 ≤ n) {k w : Nat} {op : ALUOp} (hk : ShiftOp k op) (hw : IW w) {xa y : Nat}
    {s s' : LState × Array RuleId} {v : V} (hxa : xa < s.1.nextVreg)
    (h : ApplyInternal p (sem ctx) cfg n 27 703
      [.data 59 k [], .ty (.int w), .reg (.vreg xa .int), .value y] s v s') :
    ShiftRes F isem ctx op w xa y s.1 s'.1 v := by
  have hp' := hp
  isel_split hp hc h 703
  · fb_inv [*, rule_lower_1631] at hm he
    have hdata := ‹V.data 152 35 _ = _›
    have hdj := ‹ctx.defInst? y = some _›
    have hij := ‹ctx.insts[_]? = some _›
    obtain ⟨ty, imm, hcl, hfs⟩ := defInst_iconst_clif ctx hctx hdj hij hdata.symm
    have hety : eTy ty = true := by
      have hdat := hctx.data _ _ _ hij hcl
      rw [← hdata] at hdat
      exact (fb_instData_iconst hdat).1
    simp only [List.cons.injEq, and_true] at hfs
    subst hfs
    obtain ⟨-, rfl, rfl⟩ := (ctor_imm_shift_iff ctx _ _ _ _ _).mp
      ‹externCtor ctx T.imm_shift_from_imm64 _ _ = _›
    have hA := ‹ApplyInternal _ _ _ _ 27 361 _ _ _ _›
    obtain ⟨ks, hks, rfl, m, hm', hs'⟩ := alu_rr_imm_shift_ok hp' hc (by omega) hA
    dsimp only at hm' hs'
    rw [ofV_aluRRImmShift_fb _ _ hk.ofIdx (hks.ofIdx hw)] at hm'
    cases hm'
    rw [hs']
    exact shiftRes_imm hR hk.isShift hw hdj hij hcl hety _
  · fb_inv [*, rule_lower_1622] at hm he
    have hwe := ‹CTy.int w = CTy.int 32›
    simp only [CTy.int.injEq] at hwe
    subst hwe
    have hry := ‹ctx.valueReg? y = some _›
    have hg := ‹[_][Int.toNat 0]? = some _›
    simp only [Int.toNat_zero, List.getElem?_cons_zero, Option.some.injEq] at hg
    subst hg
    obtain rfl := hctx.valueReg y _ hry
    have hA := ‹ApplyInternal _ _ _ _ 27 362 _ _ _ _›
    obtain ⟨ks, hks, rfl, m, hm', hs'⟩ := alu_rrr_ok hp' hc (by omega) hA
    dsimp only at hm' hs'
    rw [ofV_aluRRR hk.ofIdx (hks.ofIdx hw)] at hm'
    cases hm'
    rw [hs']
    exact shiftRes_rrr hR hk.isShift (by simp) _
  · fb_inv [*, rule_lower_1623] at hm he
    have hwe := ‹CTy.int w = CTy.int 64›
    simp only [CTy.int.injEq] at hwe
    subst hwe
    have hry := ‹ctx.valueReg? y = some _›
    have hg := ‹[_][Int.toNat 0]? = some _›
    simp only [Int.toNat_zero, List.getElem?_cons_zero, Option.some.injEq] at hg
    subst hg
    obtain rfl := hctx.valueReg y _ hry
    have hA := ‹ApplyInternal _ _ _ _ 27 362 _ _ _ _›
    obtain ⟨ks, hks, rfl, m, hm', hs'⟩ := alu_rrr_ok hp' hc (by omega) hA
    dsimp only at hm' hs'
    rw [ofV_aluRRR hk.ofIdx (hks.ofIdx hw)] at hm'
    cases hm'
    rw [hs']
    exact shiftRes_rrr hR hk.isShift (by simp) _
  · fb_inv [*, rule_lower_1612] at hm he
    have h16 := ‹(CTy.int w).bits ≤ 16›
    have hry := ‹ctx.valueReg? y = some _›
    have hg := ‹[_][Int.toNat 0]? = some _›
    simp only [Int.toNat_zero, List.getElem?_cons_zero, Option.some.injEq] at hg
    subst hg
    obtain rfl := hctx.valueReg y _ hry
    have hmask := ‹externCtor ctx T.shift_mask _ _ = _›
    have hA := ‹ApplyInternal _ _ _ _ 27 502 _ _ _ _›
    have hB := ‹ApplyInternal _ _ _ _ 27 362 _ _ _ _›
    have h32 : IW 32 := by simp [IW]
    rcases hw with rfl | rfl | rfl | rfl
    rotate_left 2
    · simp [CTy.bits] at h16
    · simp [CTy.bits] at h16
    all_goals first
      | (rw [ctor_shift_mask_i8_iff] at hmask) | (rw [ctor_shift_mask_i16_iff] at hmask)
    all_goals
      obtain ⟨rfl, rfl⟩ := hmask
      obtain ⟨ks1, hks1, rfl, m1, hm1, hs1⟩ := and_imm_ok hp' hc (by omega) hA
      dsimp only at hm1 hs1
      rw [ofV_aluRRImmLogic_fb _ _ (rfl : ALUOp.ofIdx? 4 = some .and) (hks1.ofIdx h32)] at hm1
      cases hm1
      obtain ⟨ks2, hks2, rfl, m2, hm2, hs2⟩ := alu_rrr_ok hp' hc (by omega) hB
      dsimp only at hm2 hs2
      rw [ofV_aluRRR hk.ofIdx (hks2.ofIdx h32)] at hm2
      cases hm2
      rw [hs2, hs1]
      exact shiftRes_mask hR hk.isShift (by simp) _ hxa rfl

end Sem

end Backend.Proof
