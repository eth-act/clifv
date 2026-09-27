import FV.Backend.Proof.IselTermsALUAMul

/-!
# `extr_32_or_64` (`lower.isle:1501`, `:1507`): forward lemmas

`bor (ishl x (iconst xs)) (ushr y (iconst ys))` (either order) at I32/I64 with
`xs + ys = ty_bits ty`, `xs, ys > 0` → `extr x, y, #ys` (`a64_extr` → `alu_rrr_shift Extr`).
The shift amounts are the constants' `u64` values that fit in `u8` (`u8_from_u64`); the three
if-lets are the `u64` arithmetic conditions (`ExtrOk`). The rule theorems are in
`IselFamALUAExtr`.
-/

namespace Backend.Proof

open Isle Isle.Interp Isle.Aarch64

/-- The conditions of the `extr` rules on the type width `w` and the two shift constants (as
`u64` values `X`, `Y`): both fit in `u8` (`u8_from_u64`), they add up to `w`, both positive. -/
def ExtrOk (w : Nat) (X Y : Int) : Prop :=
  (0 ≤ X ∧ X < 256) ∧ (0 ≤ Y ∧ Y < 256) ∧ ((w : Int) == ((u64 (X + Y) : Nat) : Int)) = true ∧
    0 < X ∧ 0 < Y

section Extern
variable (ctx : Ctx) (st : LState)

theorem ext_u8_from_u64 (i : Int) :
    externExtract ctx T.u8_from_u64 (.int i) st = if 0 ≤ i ∧ i < 256 then .ok [.int i] else .fail := rfl
theorem ctor_u8_into_u64 (a : Int) : externCtor ctx T.u8_into_u64 [.int a] st = .ok (.int a, st) := rfl
theorem ctor_u64_wrapping_add (a b : Int) :
    externCtor ctx T.u64_wrapping_add [.int a, .int b] st = .ok (.int (u64 (a + b)), st) := rfl
theorem ctor_u64_eq (a b : Int) :
    externCtor ctx T.u64_eq [.int a, .int b] st = .ok (.bool (a == b), st) := rfl
theorem ctor_u64_gt (a b : Int) :
    externCtor ctx T.u64_gt [.int a, .int b] st = .ok (.bool (decide (a > b)), st) := rfl
theorem ctor_imm_shift_from_u8 {n : Int} (h : n < 64) :
    externCtor ctx T.imm_shift_from_u8 [.int n] st = .ok (.op (.immShift n.toNat), st) := by
  show (if n < 64 then ExtResult.ok (V.op (.immShift n.toNat), st) else .fail) = _
  rw [if_pos h]
theorem ctor_a64_extr_imm_32 (s : Nat) :
    externCtor ctx T.a64_extr_imm [.ty (.int 32), .op (.immShift s)] st =
      .ok (.op (.shiftOpAndAmt ⟨.lsl, s⟩), st) := rfl
theorem ctor_a64_extr_imm_64 (s : Nat) :
    externCtor ctx T.a64_extr_imm [.ty (.int 64), .op (.immShift s)] st =
      .ok (.op (.shiftOpAndAmt ⟨.lsr, s⟩), st) := rfl
theorem beq_bool_true_true : (V.bool true == V.bool true) = true := rfl
theorem beq_bool_false_true : (V.bool false == V.bool true) = false := rfl

end Extern

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

section Rules
variable (st : LState) (tr : Array RuleId) (n : Nat)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
include hp in
theorem match_1501 {i a b x c1 y c2 w j1 j2 j3 j4 : Nat} {kx ky : Int}
    {info info1 info2 info3 info4 : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w = 32 ∨ w = 64)
    (hd : info.data = .data 152 2 [.data 151 98 [], .values [a, b]])
    (hj1 : ctx.defInst? a = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hd1 : info1.data = .data 152 2 [.data 151 103 [], .values [x, c1]])
    (hj2 : ctx.defInst? c1 = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hd2 : info2.data = .data 152 35 [.data 151 57 [], .int kx])
    (hj3 : ctx.defInst? b = some j3) (hij3 : ctx.insts[j3]? = some info3)
    (hd3 : info3.data = .data 152 2 [.data 151 104 [], .values [y, c2]])
    (hj4 : ctx.defInst? c2 = some j4) (hij4 : ctx.insts[j4]? = some info4)
    (hd4 : info4.data = .data 152 35 [.data 151 57 [], .int ky])
    (hok : ExtrOk w (u64 kx) (u64 ky)) :
    (matchRule p (sem ctx) cfg (n+20) rule_lower_1501 [.inst i]).run (st, tr) =
      .ok (some (env5 (.ty (.int w)) (.value x) (.int (u64 kx)) (.value y) (.int (u64 ky))), (st, tr)) := by
  obtain ⟨hx8, hy8, hsum, hx0, hy0⟩ := hok
  have hx0' : decide ((u64 kx : Int) > 0) = true := by simpa using hx0
  have hy0' : decide ((u64 ky : Int) > 0) = true := by simpa using hy0
  have h0 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h0
  have h1 := ext_inst_data_value ctx st hij1
  rw [hd1] at h1
  have h2 := ext_inst_data_value ctx st hij2
  rw [hd2] at h2
  have h3 := ext_inst_data_value ctx st hij3
  rw [hd3] at h3
  have h4 := ext_inst_data_value ctx st hij4
  rw [hd4] at h4
  have g1 := ext_def_inst_some ctx st hj1
  have g2 := ext_def_inst_some ctx st hj2
  have g3 := ext_def_inst_some ctx st hj3
  have g4 := ext_def_inst_some ctx st hj4
  have h5 := ext_ty_32_or_64 ctx st w
  simp only [hw, ↓reduceIte] at h5
  have he := sem_eq_beq_fa ctx
  cases hp
  isel_eval [*, rule_lower_1501, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    ctor_u8_into_u64, ctor_u64_wrapping_add, ctor_u64_eq, ctor_u64_gt, ctor_ty_bits,
    beq_bool_true_true, and_self]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
include hp in
theorem match_1501_none {i a b x c1 y c2 w j1 j2 j3 j4 : Nat} {kx ky : Int}
    {info info1 info2 info3 info4 : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w = 32 ∨ w = 64)
    (hd : info.data = .data 152 2 [.data 151 98 [], .values [a, b]])
    (hj1 : ctx.defInst? a = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hd1 : info1.data = .data 152 2 [.data 151 103 [], .values [x, c1]])
    (hj2 : ctx.defInst? c1 = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hd2 : info2.data = .data 152 35 [.data 151 57 [], .int kx])
    (hj3 : ctx.defInst? b = some j3) (hij3 : ctx.insts[j3]? = some info3)
    (hd3 : info3.data = .data 152 2 [.data 151 104 [], .values [y, c2]])
    (hj4 : ctx.defInst? c2 = some j4) (hij4 : ctx.insts[j4]? = some info4)
    (hd4 : info4.data = .data 152 35 [.data 151 57 [], .int ky])
    (hno : ¬ ExtrOk w (u64 kx) (u64 ky)) :
    (matchRule p (sem ctx) cfg (n+20) rule_lower_1501 [.inst i]).run (st, tr) = .ok (none, (st, tr)) := by
  unfold ExtrOk at hno
  have h0 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h0
  have h1 := ext_inst_data_value ctx st hij1
  rw [hd1] at h1
  have h2 := ext_inst_data_value ctx st hij2
  rw [hd2] at h2
  have h3 := ext_inst_data_value ctx st hij3
  rw [hd3] at h3
  have h4 := ext_inst_data_value ctx st hij4
  rw [hd4] at h4
  have g1 := ext_def_inst_some ctx st hj1
  have g2 := ext_def_inst_some ctx st hj2
  have g3 := ext_def_inst_some ctx st hj3
  have g4 := ext_def_inst_some ctx st hj4
  have h5 := ext_ty_32_or_64 ctx st w
  simp only [hw, ↓reduceIte] at h5
  have he := sem_eq_beq_fa ctx
  cases hp
  by_cases c1 : 0 ≤ (u64 kx : Int) ∧ (u64 kx : Int) < 256
  · by_cases c2 : 0 ≤ (u64 ky : Int) ∧ (u64 ky : Int) < 256
    · by_cases c3 : ((w : Int) == ((u64 ((u64 kx : Int) + (u64 ky : Int)) : Nat) : Int)) = true
      · by_cases c4 : 0 < (u64 kx : Int)
        · have c5 : decide ((u64 ky : Int) > 0) = false := by
            simp only [decide_eq_false_iff_not]
            exact fun h => hno (by first | exact ⟨c1, c2, c3, c4, h⟩ | exact ⟨c2, c1, c3, c4, h⟩)
          have c4' : decide ((u64 kx : Int) > 0) = true := by simpa using c4
          isel_eval [*, rule_lower_1501, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    ctor_u8_into_u64, ctor_u64_wrapping_add, ctor_u64_eq, ctor_u64_gt, ctor_ty_bits,
    beq_bool_true_true, beq_bool_false_true, and_self]
        · have c4' : decide ((u64 kx : Int) > 0) = false := by simpa using c4
          isel_eval [*, rule_lower_1501, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    ctor_u8_into_u64, ctor_u64_wrapping_add, ctor_u64_eq, ctor_u64_gt, ctor_ty_bits,
    beq_bool_true_true, beq_bool_false_true, and_self]
      · have c3' : ((w : Int) == ((u64 ((u64 kx : Int) + (u64 ky : Int)) : Nat) : Int)) = false := by
          simpa using c3
        isel_eval [*, rule_lower_1501, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    ctor_u8_into_u64, ctor_u64_wrapping_add, ctor_u64_eq, ctor_u64_gt, ctor_ty_bits,
    beq_bool_true_true, beq_bool_false_true, and_self]
    · isel_eval [*, rule_lower_1501, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    ctor_u8_into_u64, ctor_u64_wrapping_add, ctor_u64_eq, ctor_u64_gt, ctor_ty_bits,
    beq_bool_true_true, beq_bool_false_true, and_self]
  · isel_eval [*, rule_lower_1501, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    ctor_u8_into_u64, ctor_u64_wrapping_add, ctor_u64_eq, ctor_u64_gt, ctor_ty_bits,
    beq_bool_true_true, beq_bool_false_true, and_self]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
include hp in
theorem match_1507 {i a b x c1 y c2 w j1 j2 j3 j4 : Nat} {kx ky : Int}
    {info info1 info2 info3 info4 : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w = 32 ∨ w = 64)
    (hd : info.data = .data 152 2 [.data 151 98 [], .values [a, b]])
    (hj1 : ctx.defInst? a = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hd1 : info1.data = .data 152 2 [.data 151 104 [], .values [y, c1]])
    (hj2 : ctx.defInst? c1 = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hd2 : info2.data = .data 152 35 [.data 151 57 [], .int ky])
    (hj3 : ctx.defInst? b = some j3) (hij3 : ctx.insts[j3]? = some info3)
    (hd3 : info3.data = .data 152 2 [.data 151 103 [], .values [x, c2]])
    (hj4 : ctx.defInst? c2 = some j4) (hij4 : ctx.insts[j4]? = some info4)
    (hd4 : info4.data = .data 152 35 [.data 151 57 [], .int kx])
    (hok : ExtrOk w (u64 kx) (u64 ky)) :
    (matchRule p (sem ctx) cfg (n+20) rule_lower_1507 [.inst i]).run (st, tr) =
      .ok (some (env5 (.ty (.int w)) (.value y) (.int (u64 ky)) (.value x) (.int (u64 kx))), (st, tr)) := by
  obtain ⟨hx8, hy8, hsum, hx0, hy0⟩ := hok
  have hx0' : decide ((u64 kx : Int) > 0) = true := by simpa using hx0
  have hy0' : decide ((u64 ky : Int) > 0) = true := by simpa using hy0
  have h0 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h0
  have h1 := ext_inst_data_value ctx st hij1
  rw [hd1] at h1
  have h2 := ext_inst_data_value ctx st hij2
  rw [hd2] at h2
  have h3 := ext_inst_data_value ctx st hij3
  rw [hd3] at h3
  have h4 := ext_inst_data_value ctx st hij4
  rw [hd4] at h4
  have g1 := ext_def_inst_some ctx st hj1
  have g2 := ext_def_inst_some ctx st hj2
  have g3 := ext_def_inst_some ctx st hj3
  have g4 := ext_def_inst_some ctx st hj4
  have h5 := ext_ty_32_or_64 ctx st w
  simp only [hw, ↓reduceIte] at h5
  have he := sem_eq_beq_fa ctx
  cases hp
  isel_eval [*, rule_lower_1507, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    ctor_u8_into_u64, ctor_u64_wrapping_add, ctor_u64_eq, ctor_u64_gt, ctor_ty_bits,
    beq_bool_true_true, beq_bool_false_true, and_self]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
include hp in
theorem match_1507_none {i a b x c1 y c2 w j1 j2 j3 j4 : Nat} {kx ky : Int}
    {info info1 info2 info3 info4 : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w = 32 ∨ w = 64)
    (hd : info.data = .data 152 2 [.data 151 98 [], .values [a, b]])
    (hj1 : ctx.defInst? a = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hd1 : info1.data = .data 152 2 [.data 151 104 [], .values [y, c1]])
    (hj2 : ctx.defInst? c1 = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hd2 : info2.data = .data 152 35 [.data 151 57 [], .int ky])
    (hj3 : ctx.defInst? b = some j3) (hij3 : ctx.insts[j3]? = some info3)
    (hd3 : info3.data = .data 152 2 [.data 151 103 [], .values [x, c2]])
    (hj4 : ctx.defInst? c2 = some j4) (hij4 : ctx.insts[j4]? = some info4)
    (hd4 : info4.data = .data 152 35 [.data 151 57 [], .int kx])
    (hno : ¬ ExtrOk w (u64 kx) (u64 ky)) :
    (matchRule p (sem ctx) cfg (n+20) rule_lower_1507 [.inst i]).run (st, tr) = .ok (none, (st, tr)) := by
  unfold ExtrOk at hno
  have h0 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h0
  have h1 := ext_inst_data_value ctx st hij1
  rw [hd1] at h1
  have h2 := ext_inst_data_value ctx st hij2
  rw [hd2] at h2
  have h3 := ext_inst_data_value ctx st hij3
  rw [hd3] at h3
  have h4 := ext_inst_data_value ctx st hij4
  rw [hd4] at h4
  have g1 := ext_def_inst_some ctx st hj1
  have g2 := ext_def_inst_some ctx st hj2
  have g3 := ext_def_inst_some ctx st hj3
  have g4 := ext_def_inst_some ctx st hj4
  have h5 := ext_ty_32_or_64 ctx st w
  simp only [hw, ↓reduceIte] at h5
  have he := sem_eq_beq_fa ctx
  cases hp
  by_cases c1 : 0 ≤ (u64 ky : Int) ∧ (u64 ky : Int) < 256
  · by_cases c2 : 0 ≤ (u64 kx : Int) ∧ (u64 kx : Int) < 256
    · by_cases c3 : ((w : Int) == ((u64 ((u64 kx : Int) + (u64 ky : Int)) : Nat) : Int)) = true
      · by_cases c4 : 0 < (u64 kx : Int)
        · have c5 : decide ((u64 ky : Int) > 0) = false := by
            simp only [decide_eq_false_iff_not]
            exact fun h => hno (by first | exact ⟨c1, c2, c3, c4, h⟩ | exact ⟨c2, c1, c3, c4, h⟩)
          have c4' : decide ((u64 kx : Int) > 0) = true := by simpa using c4
          isel_eval [*, rule_lower_1507, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    ctor_u8_into_u64, ctor_u64_wrapping_add, ctor_u64_eq, ctor_u64_gt, ctor_ty_bits,
    beq_bool_true_true, beq_bool_false_true, and_self]
        · have c4' : decide ((u64 kx : Int) > 0) = false := by simpa using c4
          isel_eval [*, rule_lower_1507, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    ctor_u8_into_u64, ctor_u64_wrapping_add, ctor_u64_eq, ctor_u64_gt, ctor_ty_bits,
    beq_bool_true_true, beq_bool_false_true, and_self]
      · have c3' : ((w : Int) == ((u64 ((u64 kx : Int) + (u64 ky : Int)) : Nat) : Int)) = false := by
          simpa using c3
        isel_eval [*, rule_lower_1507, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    ctor_u8_into_u64, ctor_u64_wrapping_add, ctor_u64_eq, ctor_u64_gt, ctor_ty_bits,
    beq_bool_true_true, beq_bool_false_true, and_self]
    · isel_eval [*, rule_lower_1507, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    ctor_u8_into_u64, ctor_u64_wrapping_add, ctor_u64_eq, ctor_u64_gt, ctor_ty_bits,
    beq_bool_true_true, beq_bool_false_true, and_self]
  · isel_eval [*, rule_lower_1507, ext_value_array_2, ext_u64_from_imm64, ext_u8_from_u64,
    ctor_u8_into_u64, ctor_u64_wrapping_add, ctor_u64_eq, ctor_u64_gt, ctor_ty_bits,
    beq_bool_true_true, beq_bool_false_true, and_self]

include hp in
theorem match_1501_ty {i a b w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : ¬ (w = 32 ∨ w = 64))
    (hd : info.data = .data 152 2 [.data 151 98 [], .values [a, b]]) :
    (matchRule p (sem ctx) cfg (n+20) rule_lower_1501 [.inst i]).run (st, tr) = .ok (none, (st, tr)) := by
  have h0 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h0
  have h5 := ext_ty_32_or_64 ctx st w
  simp only [hw, ↓reduceIte] at h5
  cases hp
  isel_eval [*, rule_lower_1501]

include hp in
theorem match_1507_ty {i a b w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : ¬ (w = 32 ∨ w = 64))
    (hd : info.data = .data 152 2 [.data 151 98 [], .values [a, b]]) :
    (matchRule p (sem ctx) cfg (n+20) rule_lower_1507 [.inst i]).run (st, tr) = .ok (none, (st, tr)) := by
  have h0 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h0
  have h5 := ext_ty_32_or_64 ctx st w
  simp only [hw, ↓reduceIte] at h5
  cases hp
  isel_eval [*, rule_lower_1507]

end Rules

/-! ## `a64_extr` and the right-hand sides -/

section Rhs
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp hc in
theorem a64_extr_run_32 (a b : Reg) (s : Nat) :
    (applyTerm p (sem ctx) cfg (n+30) 27 515 [.ty (.int 32), .reg a, .reg b, .op (.immShift s)]).run
      (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRRShift .extr .size32 (st.fresh .int).1 a b ⟨.lsl, s⟩),
          ((tr.push rule_inst_1592.id).push rule_inst_2656.id).push rule_inst_3487.id)) := by
  have h := fun st tr n => alu_rrr_shift_run hp ctx hc st tr n
    (fun st tr n => operand_size_32 hp ctx hc st tr n (w := 32) (by decide)) (k := 15) (op := .extr) rfl rfl
  have h1 := fun st => ctor_a64_extr_imm_32 ctx st s
  cases hp
  isel_eval [*, rule_inst_3487]

include hp hc in
theorem a64_extr_run_64 (a b : Reg) (s : Nat) :
    (applyTerm p (sem ctx) cfg (n+30) 27 515 [.ty (.int 64), .reg a, .reg b, .op (.immShift s)]).run
      (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRRShift .extr .size64 (st.fresh .int).1 a b ⟨.lsr, s⟩),
          ((tr.push rule_inst_1593.id).push rule_inst_2656.id).push rule_inst_3487.id)) := by
  have h := fun st tr n => alu_rrr_shift_run hp ctx hc st tr n
    (fun st tr n => operand_size_64 hp ctx hc st tr n (w := 64) (by decide) (Nat.le_refl 64)) (k := 15)
    (op := .extr) rfl rfl
  have h1 := fun st => ctor_a64_extr_imm_64 ctx st s
  cases hp
  isel_eval [*, rule_inst_3487]

include hp hc in
theorem rhs_1501 {x y w : Nat} {X Y : Int} {rx ry : Reg} (hx : ctx.valueReg? x = some rx)
    (hy : ctx.valueReg? y = some ry) (hw : w = 32 ∨ w = 64) (hY : Y < 64) :
    ∃ tr' sh, sh.amt = Y.toNat ∧ (evalExpr p (sem ctx) cfg (n+60) rule_lower_1501.rhs
        (env5 (.ty (.int w)) (.value x) (.int X) (.value y) (.int Y))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRRShift .extr (szOf w) (st.fresh .int).1 rx ry sh), tr')) := by
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  have h3 := fun st => ctor_imm_shift_from_u8 ctx st hY
  rcases hw with rfl | rfl
  · have h1 := fun st tr n => a64_extr_run_32 hp ctx hc st tr n
    cases hp
    refine Exists.intro ?w (Exists.intro ⟨.lsl, Y.toNat⟩ ⟨rfl, ?h⟩)
    case h =>
      isel_eval [*, rule_lower_1501, ctor_put_in_reg ctx _ hx, ctor_put_in_reg ctx _ hy]
      rfl
  · have h1 := fun st tr n => a64_extr_run_64 hp ctx hc st tr n
    cases hp
    refine Exists.intro ?w2 (Exists.intro ⟨.lsr, Y.toNat⟩ ⟨rfl, ?h2⟩)
    case h2 =>
      isel_eval [*, rule_lower_1501, ctor_put_in_reg ctx _ hx, ctor_put_in_reg ctx _ hy]
      rfl

include hp in
theorem rhs_1501_none {x y w : Nat} {X Y : Int}
    (hxy : ctx.valueReg? x = none ∨ ctx.valueReg? y = none) (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+60) rule_lower_1501.rhs (env5 (.ty (.int w)) (.value x) (.int X) (.value y) (.int Y))).run (st, tr) ≠ .ok (some v, s') := by
  cases hp
  rcases hxy with hx | hy
  · isel_eval [*, rule_lower_1501, ctor_put_in_reg_none ctx _ hx]
    exact fun h => by cases h
  · cases hx : ctx.valueReg? x with
    | none =>
      isel_eval [*, rule_lower_1501, ctor_put_in_reg_none ctx _ hx]
      exact fun h => by cases h
    | some rx =>
      isel_eval [*, rule_lower_1501, ctor_put_in_reg ctx _ hx, ctor_put_in_reg_none ctx _ hy]
      exact fun h => by cases h

include hp hc in
theorem rhs_1507 {x y w : Nat} {X Y : Int} {rx ry : Reg} (hx : ctx.valueReg? x = some rx)
    (hy : ctx.valueReg? y = some ry) (hw : w = 32 ∨ w = 64) (hY : Y < 64) :
    ∃ tr' sh, sh.amt = Y.toNat ∧ (evalExpr p (sem ctx) cfg (n+60) rule_lower_1507.rhs
        (env5 (.ty (.int w)) (.value y) (.int Y) (.value x) (.int X))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRRShift .extr (szOf w) (st.fresh .int).1 rx ry sh), tr')) := by
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  have h3 := fun st => ctor_imm_shift_from_u8 ctx st hY
  rcases hw with rfl | rfl
  · have h1 := fun st tr n => a64_extr_run_32 hp ctx hc st tr n
    cases hp
    refine Exists.intro ?w (Exists.intro ⟨.lsl, Y.toNat⟩ ⟨rfl, ?h⟩)
    case h =>
      isel_eval [*, rule_lower_1507, ctor_put_in_reg ctx _ hx, ctor_put_in_reg ctx _ hy]
      rfl
  · have h1 := fun st tr n => a64_extr_run_64 hp ctx hc st tr n
    cases hp
    refine Exists.intro ?w2 (Exists.intro ⟨.lsr, Y.toNat⟩ ⟨rfl, ?h2⟩)
    case h2 =>
      isel_eval [*, rule_lower_1507, ctor_put_in_reg ctx _ hx, ctor_put_in_reg ctx _ hy]
      rfl

include hp in
theorem rhs_1507_none {x y w : Nat} {X Y : Int}
    (hxy : ctx.valueReg? x = none ∨ ctx.valueReg? y = none) (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+60) rule_lower_1507.rhs (env5 (.ty (.int w)) (.value y) (.int Y) (.value x) (.int X))).run (st, tr) ≠ .ok (some v, s') := by
  cases hp
  rcases hxy with hx | hy
  · isel_eval [*, rule_lower_1507, ctor_put_in_reg_none ctx _ hx]
    exact fun h => by cases h
  · cases hx : ctx.valueReg? x with
    | none =>
      isel_eval [*, rule_lower_1507, ctor_put_in_reg_none ctx _ hx]
      exact fun h => by cases h
    | some rx =>
      isel_eval [*, rule_lower_1507, ctor_put_in_reg ctx _ hx, ctor_put_in_reg_none ctx _ hy]
      exact fun h => by cases h

end Rhs

end Backend.Proof
