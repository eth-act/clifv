import FV.Backend.Proof.IselTermsALUAExtr

/-!
# Narrow `smulhi`/`umulhi` (`lower.isle:1059`, `:1071`): forward lemmas

`put_in_reg_sext64 x` / `put_in_reg_zext64 x` (terms 557/558, two rules each) dispatch on
`value_type x`: a type of at most 32 bits → `extend x` to 64 bits (`sxt*`/`uxt*`), `I64` → the
register of `x`, anything else → no match. The rules then emit `madd x64, y64, xzr` and an
`asr`/`lsr` by the type width (`alu_rr_imm_shift`). The rule theorems are in `IselFamALUAMulN`.
-/

namespace Backend.Proof

open Isle Isle.Interp Isle.Aarch64

section Extern
variable (ctx : Ctx) (st : LState)

theorem ext_fits_in_32_ty (t : CTy) :
    externExtract ctx T.fits_in_32 (.ty t) st = if t.bits ≤ 32 then .ok [.ty t] else .fail := by
  have : externExtract ctx T.fits_in_32 (.ty t) st =
    if decide (t.bits ≤ 32) = true then .ok [.ty t] else .fail := rfl
  rw [this]; by_cases h : t.bits ≤ 32 <;> simp [h]

theorem ctor_ty_bits_ty (t : CTy) : externCtor ctx T.ty_bits [.ty t] st = .ok (.int t.bits, st) := rfl

theorem ofV_extend (rd rn : Reg) (sg : Bool) (a b : Nat) :
    MInst.ofV (.data 58 28 [.reg rd, .reg rn, .bool sg, .int a, .int b]) =
      some (.extend rd rn sg a b) := by
  have e1 : MInst.ofV (.data 58 28 [.reg rd, .reg rn, .bool sg, .int a, .int b]) =
      (do
        let r1 ← (V.reg rd).reg?
        let r2 ← (V.reg rn).reg?
        let s ← (V.bool sg).bool?
        let a' ← (V.int a).nat?
        let b' ← (V.int b).nat?
        return .extend r1 r2 s a' b') := rfl
  have e2 : ∀ c : Nat, (V.int c).nat? = some c := fun c => by simp [V.nat?]
  rw [e1, e2, e2]
  rfl

theorem beq_ty_i64 : (V.ty (.int 64) == V.ty (.int 64)) = true := rfl

theorem beq_ty_ne_i64 {t : CTy} (h : t ≠ .int 64) : (V.ty t == V.ty (.int 64)) = false := by
  cases t <;> simp_all


theorem ext_value_type_none {v : Nat} (h : ctx.valueType? v = none) :
    externExtract ctx T.value_type (.value v) st = .unmodeled s!"value_type of unknown v{v}" := by
  have : externExtract ctx T.value_type (.value v) st = match ctx.valueType? v with
    | some ty => .ok [.ty ty]
    | none => .unmodeled s!"value_type of unknown v{v}" := rfl
  rw [this, h]

end Extern

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

section Helpers
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp hc in
theorem extend_run (r : Reg) (sg : Bool) (a b : Nat) :
    (applyTerm p (sem ctx) cfg (n+20) 27 417 [.reg r, .bool sg, .int a, .int b]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.extend (st.fresh .int).1 r sg a b), tr.push rule_inst_2991.id)) := by
  have hemit := fun st rd rn => ctor_emit ctx st (ofV_extend rd rn sg a b)
  cases hp
  isel_eval [*, rule_inst_2991, ctor_temp_writable_reg_i64, ctor_writable_reg_to_reg]

include hp hc in
/-- `alu_rr_imm_shift op I64 x imm`. -/
theorem alu_rr_imm_shift_run {k : Nat} {op : ALUOp} (hk : ALUOp.ofIdx? k = some op) (a : Reg)
    (s : Nat) :
    (applyTerm p (sem ctx) cfg (n+20) 27 361 [.data 59 k [], .ty (.int 64), .reg a, .op (.immShift s)]).run
      (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRImmShift op .size64 (st.fresh .int).1 a s),
          (tr.push rule_inst_1593.id).push rule_inst_2537.id)) := by
  have hsz := fun st tr n => operand_size_64 hp ctx hc st tr n (w := 64) (by decide) (Nat.le_refl 64)
  have hemit := fun st rd rn => ctor_emit ctx st (ofV_aluRRImmShift hk (ks := 1) (sz := .size64) rfl rd rn s)
  cases hp
  isel_eval [*, rule_inst_2537, ctor_temp_writable_reg_i64, ctor_writable_reg_to_reg]

include hp hc in
theorem asr_imm_run (a : Reg) (s : Nat) :
    (applyTerm p (sem ctx) cfg (n+30) 27 487 [.ty (.int 64), .reg a, .op (.immShift s)]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRImmShift .asr .size64 (st.fresh .int).1 a s),
          ((tr.push rule_inst_1593.id).push rule_inst_2537.id).push rule_inst_3366.id)) := by
  have h := fun st tr n => alu_rr_imm_shift_run hp ctx hc st tr n (k := 17) (op := .asr) rfl a s
  cases hp
  isel_eval [*, rule_inst_3366]

include hp hc in
theorem lsr_imm_run (a : Reg) (s : Nat) :
    (applyTerm p (sem ctx) cfg (n+30) 27 489 [.ty (.int 64), .reg a, .op (.immShift s)]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRImmShift .lsr .size64 (st.fresh .int).1 a s),
          ((tr.push rule_inst_1593.id).push rule_inst_2537.id).push rule_inst_3375.id)) := by
  have h := fun st tr n => alu_rr_imm_shift_run hp ctx hc st tr n (k := 16) (op := .lsr) rfl a s
  cases hp
  isel_eval [*, rule_inst_3375]

end Helpers

/-! ## `put_in_reg_sext64` (557) and `put_in_reg_zext64` (558) -/

section Ext64
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp hc in
theorem sext64_run_narrow {x : Nat} {t : CTy} {rx : Reg} (hvt : ctx.valueType? x = some t)
    (h32 : t.bits ≤ 32) (hx : ctx.valueReg? x = some rx) :
    ∃ tr', (applyTerm p (sem ctx) cfg (n+60) 27 557 [.value x]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.extend (st.fresh .int).1 rx true t.bits 64), tr')) := by
  have h1 : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+20) 27 417
      [.reg rx, .bool true, .int t.bits, .int 64]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.extend (st.fresh .int).1 rx true t.bits 64), tr.push rule_inst_2991.id)) :=
    fun st tr n => extend_run hp ctx hc st tr n rx true t.bits 64
  have h2 := ext_value_type ctx st hvt
  have h3 := ext_fits_in_32_ty ctx st t
  simp only [h32, ↓reduceIte] at h3
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_inst_3819, rule_inst_3823, ctor_put_in_reg ctx _ hx, ctor_ty_bits_ty]
    rfl

include hp hc in
theorem sext64_run_64 {x : Nat} {rx : Reg} (hvt : ctx.valueType? x = some (.int 64))
    (hx : ctx.valueReg? x = some rx) :
    ∃ tr', (applyTerm p (sem ctx) cfg (n+60) 27 557 [.value x]).run (st, tr) =
      .ok (some (.reg rx), (st, tr')) := by
  have h2 := ext_value_type ctx st hvt
  have h3 := ext_fits_in_32_ty ctx st (.int 64)
  simp only [CTy.bits] at h3
  have he := sem_eq_beq_fa ctx
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_inst_3819, rule_inst_3823, ctor_put_in_reg ctx _ hx, beq_ty_i64]
    rfl

include hp hc in
theorem zext64_run_narrow {x : Nat} {t : CTy} {rx : Reg} (hvt : ctx.valueType? x = some t)
    (h32 : t.bits ≤ 32) (hx : ctx.valueReg? x = some rx) :
    ∃ tr', (applyTerm p (sem ctx) cfg (n+60) 27 558 [.value x]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.extend (st.fresh .int).1 rx false t.bits 64), tr')) := by
  have h1 : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+20) 27 417
      [.reg rx, .bool false, .int t.bits, .int 64]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.extend (st.fresh .int).1 rx false t.bits 64), tr.push rule_inst_2991.id)) :=
    fun st tr n => extend_run hp ctx hc st tr n rx false t.bits 64
  have h2 := ext_value_type ctx st hvt
  have h3 := ext_fits_in_32_ty ctx st t
  simp only [h32, ↓reduceIte] at h3
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_inst_3829, rule_inst_3833, ctor_put_in_reg ctx _ hx, ctor_ty_bits_ty]
    rfl

include hp hc in
theorem zext64_run_64 {x : Nat} {rx : Reg} (hvt : ctx.valueType? x = some (.int 64))
    (hx : ctx.valueReg? x = some rx) :
    ∃ tr', (applyTerm p (sem ctx) cfg (n+60) 27 558 [.value x]).run (st, tr) =
      .ok (some (.reg rx), (st, tr')) := by
  have h2 := ext_value_type ctx st hvt
  have h3 := ext_fits_in_32_ty ctx st (.int 64)
  simp only [CTy.bits] at h3
  have he := sem_eq_beq_fa ctx
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_inst_3829, rule_inst_3833, ctor_put_in_reg ctx _ hx, beq_ty_i64]
    rfl

include hp in
theorem sext64_run_novt {x : Nat} (hvt : ctx.valueType? x = none) (a : V) (s : LState × Array RuleId) :
    (applyTerm p (sem ctx) cfg (n+60) 27 557 [.value x]).run (st, tr) ≠ .ok (some a, s) := by
  have h2 := ext_value_type_none ctx st hvt
  cases hp
  isel_eval [*, rule_inst_3819, rule_inst_3823]
  exact fun h => by cases h

include hp hc in
theorem sext64_run_other {x : Nat} {t : CTy} (hvt : ctx.valueType? x = some t) (h32 : ¬ t.bits ≤ 32)
    (h64 : t ≠ .int 64) (a : V) (s : LState × Array RuleId) :
    (applyTerm p (sem ctx) cfg (n+60) 27 557 [.value x]).run (st, tr) ≠ .ok (some a, s) := by
  have h2 := ext_value_type ctx st hvt
  have h3 := ext_fits_in_32_ty ctx st t
  simp only [h32, ↓reduceIte] at h3
  have he := sem_eq_beq_fa ctx
  have hne := beq_ty_ne_i64 h64
  cases hp
  isel_eval [*, rule_inst_3819, rule_inst_3823]
  exact fun h => by cases h

include hp in
theorem zext64_run_novt {x : Nat} (hvt : ctx.valueType? x = none) (a : V) (s : LState × Array RuleId) :
    (applyTerm p (sem ctx) cfg (n+60) 27 558 [.value x]).run (st, tr) ≠ .ok (some a, s) := by
  have h2 := ext_value_type_none ctx st hvt
  cases hp
  isel_eval [*, rule_inst_3829, rule_inst_3833]
  exact fun h => by cases h

include hp hc in
theorem zext64_run_other {x : Nat} {t : CTy} (hvt : ctx.valueType? x = some t) (h32 : ¬ t.bits ≤ 32)
    (h64 : t ≠ .int 64) (a : V) (s : LState × Array RuleId) :
    (applyTerm p (sem ctx) cfg (n+60) 27 558 [.value x]).run (st, tr) ≠ .ok (some a, s) := by
  have h2 := ext_value_type ctx st hvt
  have h3 := ext_fits_in_32_ty ctx st t
  simp only [h32, ↓reduceIte] at h3
  have he := sem_eq_beq_fa ctx
  have hne := beq_ty_ne_i64 h64
  cases hp
  isel_eval [*, rule_inst_3829, rule_inst_3833]
  exact fun h => by cases h

end Ext64

/-! ## Contracts of `put_in_reg_sext64` / `put_in_reg_zext64` -/

section Contract
variable {f : Clif.Function} (hctx : CtxInv f ctx) (st : LState) (tr : Array RuleId) (n : Nat)

include hp hc hctx in
/-- **`put_in_reg_sext64 x` returned `a`**: `x` has a type `t`; if `t` has at most 32 bits, `a`
is a fresh vreg written by `sxt` from `t.bits` to 64 bits, if `t = I64`, `a` is `x`'s register. -/
theorem sext64_inv {x : Nat} {a : V} {st2 : LState} {tr2 : Array RuleId}
    (h : (applyTerm p (sem ctx) cfg (n+60) 27 557 [.value x]).run (st, tr) = .ok (some a, (st2, tr2))) :
    ∃ t, ctx.valueType? x = some t ∧ ctx.valueReg? x = some (.vreg x .int) ∧
      ((t.bits ≤ 32 ∧ a = .reg (st.fresh .int).1 ∧
          st2 = (st.fresh .int).2.emit (.extend (st.fresh .int).1 (.vreg x .int) true t.bits 64)) ∨
        (t = .int 64 ∧ a = .reg (.vreg x .int) ∧ st2 = st)) := by
  cases hvt : ctx.valueType? x with
  | none => exact absurd h (sext64_run_novt hp ctx st tr n hvt _ _)
  | some t =>
  have hx := hctx.typedReg x t hvt
  refine ⟨t, rfl, hx, ?_⟩
  by_cases h32 : t.bits ≤ 32
  · obtain ⟨tr', he⟩ := sext64_run_narrow hp ctx hc st tr n hvt h32 hx
    rw [he] at h
    simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact .inl ⟨h32, rfl, rfl⟩
  · by_cases h64 : t = .int 64
    · subst h64
      obtain ⟨tr', he⟩ := sext64_run_64 hp ctx hc st tr n hvt hx
      rw [he] at h
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact .inr ⟨rfl, rfl, rfl⟩
    · exact absurd h (sext64_run_other hp ctx hc st tr n hvt h32 h64 _ _)

include hp hc hctx in
theorem zext64_inv {x : Nat} {a : V} {st2 : LState} {tr2 : Array RuleId}
    (h : (applyTerm p (sem ctx) cfg (n+60) 27 558 [.value x]).run (st, tr) = .ok (some a, (st2, tr2))) :
    ∃ t, ctx.valueType? x = some t ∧ ctx.valueReg? x = some (.vreg x .int) ∧
      ((t.bits ≤ 32 ∧ a = .reg (st.fresh .int).1 ∧
          st2 = (st.fresh .int).2.emit (.extend (st.fresh .int).1 (.vreg x .int) false t.bits 64)) ∨
        (t = .int 64 ∧ a = .reg (.vreg x .int) ∧ st2 = st)) := by
  cases hvt : ctx.valueType? x with
  | none => exact absurd h (zext64_run_novt hp ctx st tr n hvt _ _)
  | some t =>
  have hx := hctx.typedReg x t hvt
  refine ⟨t, rfl, hx, ?_⟩
  by_cases h32 : t.bits ≤ 32
  · obtain ⟨tr', he⟩ := zext64_run_narrow hp ctx hc st tr n hvt h32 hx
    rw [he] at h
    simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact .inl ⟨h32, rfl, rfl⟩
  · by_cases h64 : t = .int 64
    · subst h64
      obtain ⟨tr', he⟩ := zext64_run_64 hp ctx hc st tr n hvt hx
      rw [he] at h
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact .inr ⟨rfl, rfl, rfl⟩
    · exact absurd h (zext64_run_other hp ctx hc st tr n hvt h32 h64 _ _)

end Contract

/-! ## The root rules: match phase and right-hand side -/

/-- The seven-variable environment of the narrow `mulhi` rules after the match. -/
abbrev env7 (a b c : V) : Interp.Env V :=
  (((Array.replicate 7 none).setIfInBounds 0 (some a)).setIfInBounds 1 (some b)).setIfInBounds 2
    (some c)

section Roots
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp in
theorem match_1059 {i x y w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 32)
    (hd : info.data = .data 152 2 [.data 151 79 [], .values [x, y]]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1059 [.inst i]).run (st, tr) =
      .ok (some (env7 (.ty (.int w)) (.value x) (.value y)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_32 ctx st w
  simp only [hw, ↓reduceIte] at h2
  cases hp
  isel_eval [*, rule_lower_1059, ext_value_array_2]

include hp in
theorem match_1059_ty {i x y w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : ¬ w ≤ 32)
    (hd : info.data = .data 152 2 [.data 151 79 [], .values [x, y]]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1059 [.inst i]).run (st, tr) = .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_32 ctx st w
  simp only [hw, ↓reduceIte] at h2
  cases hp
  isel_eval [*, rule_lower_1059]

include hp in
theorem match_1071 {i x y w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 32)
    (hd : info.data = .data 152 2 [.data 151 78 [], .values [x, y]]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1071 [.inst i]).run (st, tr) =
      .ok (some (env7 (.ty (.int w)) (.value x) (.value y)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_32 ctx st w
  simp only [hw, ↓reduceIte] at h2
  cases hp
  isel_eval [*, rule_lower_1071, ext_value_array_2]

include hp in
theorem match_1071_ty {i x y w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : ¬ w ≤ 32)
    (hd : info.data = .data 152 2 [.data 151 78 [], .values [x, y]]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1071 [.inst i]).run (st, tr) = .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_32 ctx st w
  simp only [hw, ↓reduceIte] at h2
  cases hp
  isel_eval [*, rule_lower_1071]

include hp hc in
/-- The right-hand side of rule 1059 from the results of the two `put_in_reg_*ext64` calls. -/
theorem rhs_1059 {x y w : Nat} {r1 r2 : Reg} {s1 s2 : LState} {t1 t2 : Array RuleId} (hw : w ≤ 32)
    (h1 : (applyTerm p (sem ctx) cfg (n+97) 27 557 [.value x]).run (st, tr) = .ok (some (.reg r1), (s1, t1)))
    (h2 : (applyTerm p (sem ctx) cfg (n+96) 27 557 [.value y]).run (s1, t1) = .ok (some (.reg r2), (s2, t2))) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+100) rule_lower_1059.rhs (env7 (.ty (.int w)) (.value x) (.value y))).run
        (st, tr) =
      .ok (some (.regsVec [[((s2.fresh .int).2.emit (.aluRRRR .mAdd .size64 (s2.fresh .int).1 r1 r2 .xzr)).fresh .int |>.1]]),
        ((((s2.fresh .int).2.emit (.aluRRRR .mAdd .size64 (s2.fresh .int).1 r1 r2 .xzr)).fresh .int).2.emit
          (.aluRRImmShift .asr .size64
            (((s2.fresh .int).2.emit (.aluRRRR .mAdd .size64 (s2.fresh .int).1 r1 r2 .xzr)).fresh .int).1
            (s2.fresh .int).1 w), tr')) := by
  have h3 := fun st tr n => madd_run hp ctx hc st tr n (w := 64)
    (fun st tr n => operand_size_64 hp ctx hc st tr n (w := 64) (by decide) (Nat.le_refl 64))
    (ks := 1) (sz := .size64) rfl
  have h4 := fun st tr n => asr_imm_run hp ctx hc st tr n
  have h5 := fun st tr n => output_reg_run hp ctx hc st tr n
  have h6 := fun st => ctor_imm_shift_from_u8 ctx st (n := (w : Int)) (by omega)
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_1059, ctor_zero_reg, ctor_ty_bits]
    rfl

include hp hc in
/-- The right-hand side of rule 1071 from the results of the two `put_in_reg_*ext64` calls. -/
theorem rhs_1071 {x y w : Nat} {r1 r2 : Reg} {s1 s2 : LState} {t1 t2 : Array RuleId} (hw : w ≤ 32)
    (h1 : (applyTerm p (sem ctx) cfg (n+97) 27 558 [.value x]).run (st, tr) = .ok (some (.reg r1), (s1, t1)))
    (h2 : (applyTerm p (sem ctx) cfg (n+96) 27 558 [.value y]).run (s1, t1) = .ok (some (.reg r2), (s2, t2))) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+100) rule_lower_1071.rhs (env7 (.ty (.int w)) (.value x) (.value y))).run
        (st, tr) =
      .ok (some (.regsVec [[((s2.fresh .int).2.emit (.aluRRRR .mAdd .size64 (s2.fresh .int).1 r1 r2 .xzr)).fresh .int |>.1]]),
        ((((s2.fresh .int).2.emit (.aluRRRR .mAdd .size64 (s2.fresh .int).1 r1 r2 .xzr)).fresh .int).2.emit
          (.aluRRImmShift .lsr .size64
            (((s2.fresh .int).2.emit (.aluRRRR .mAdd .size64 (s2.fresh .int).1 r1 r2 .xzr)).fresh .int).1
            (s2.fresh .int).1 w), tr')) := by
  have h3 := fun st tr n => madd_run hp ctx hc st tr n (w := 64)
    (fun st tr n => operand_size_64 hp ctx hc st tr n (w := 64) (by decide) (Nat.le_refl 64))
    (ks := 1) (sz := .size64) rfl
  have h4 := fun st tr n => lsr_imm_run hp ctx hc st tr n
  have h6 := fun st => ctor_imm_shift_from_u8 ctx st (n := (w : Int)) (by omega)
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_1071, ctor_zero_reg, ctor_ty_bits, ctor_value_reg, ctor_output]
    rfl

end Roots

end Backend.Proof
