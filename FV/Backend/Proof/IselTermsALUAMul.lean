import FV.Backend.Proof.IselTermsLogicNot

/-!
# Multiplication rules of family A: forward lemmas

`smulhi_64`/`umulhi_64` (`lower.isle:1056`/`:1068`: `smulh`/`umulh` via `alu_rrr`),
`imul_base_case` (`:871`: `madd x, y, xzr`), and the multiply-add fusions `iadd_imul_right`
(`:125`), `iadd_imul_left` (`:128`), `isub_imul` (`:132`) (`madd`/`msub` via `alu_rrrr`).
The helper contracts `alu_rrrr_run`, `madd_run`, `msub_run` are generic in the operand size
(`operand_size_run`). The rule theorems are in `IselFamALUAMul`.
-/

namespace Backend.Proof

open Isle Isle.Interp Isle.Aarch64

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

/-- A two-variable rule environment as the matcher builds it. -/
abbrev env2a (a b : V) : Interp.Env V :=
  ((Array.replicate 2 none).setIfInBounds 0 (some a)).setIfInBounds 1 (some b)

theorem sem_eq_beq_fa (a b : V) : (sem ctx).eq a b = (a == b) := rfl

theorem ctor_zero_reg_fa (st : LState) : externCtor ctx T.zero_reg [] st = .ok (.reg .xzr, st) := rfl

/-! ## `alu_rrrr`, `madd`, `msub`; `smulh`, `umulh` -/

section Helpers
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp hc in
theorem alu_rrrr_run {k ks : Nat} {op : ALUOp3} {sz : OperandSize} {w : Nat} {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 ks []), (st, tr.push rid)))
    (hk : ALUOp3.ofIdx? k = some op) (hs : OperandSize.ofIdx? ks = some sz) (a b c : Reg) :
    (applyTerm p (sem ctx) cfg (n+20) 27 382 [.data 60 k [], .ty (.int w), .reg a, .reg b, .reg c]).run
      (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRRR op sz (st.fresh .int).1 a b c),
          (tr.push rid).push rule_inst_2701.id)) := by
  have hemit := fun st rd rn rm ra => ctor_emit ctx st (ofV_aluRRRR hk hs rd rn rm ra)
  cases hp
  isel_eval [*, rule_inst_2701, ctor_temp_writable_reg_i64, ctor_writable_reg_to_reg]

include hp hc in
/-- `madd ty x y z` (`(alu_rrrr (ALUOp3.MAdd) ty x y z)`: `z + x * y`). -/
theorem madd_run {ks : Nat} {sz : OperandSize} {w : Nat} {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 ks []), (st, tr.push rid)))
    (hs : OperandSize.ofIdx? ks = some sz) (a b c : Reg) :
    (applyTerm p (sem ctx) cfg (n+30) 27 443 [.ty (.int w), .reg a, .reg b, .reg c]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRRR .mAdd sz (st.fresh .int).1 a b c),
          ((tr.push rid).push rule_inst_2701.id).push rule_inst_3177.id)) := by
  have h := fun st tr n => alu_rrrr_run hp ctx hc st tr n hsz (k := 0) rfl hs
  cases hp
  isel_eval [*, rule_inst_3177]

include hp hc in
/-- `msub ty x y z` (`(alu_rrrr (ALUOp3.MSub) ty x y z)`: `z - x * y`). -/
theorem msub_run {ks : Nat} {sz : OperandSize} {w : Nat} {rid : RuleId}
    (hsz : ∀ st tr n, (applyTerm p (sem ctx) cfg (n+8) 93 305 [.ty (.int w)]).run (st, tr) =
      .ok (some (.data 93 ks []), (st, tr.push rid)))
    (hs : OperandSize.ofIdx? ks = some sz) (a b c : Reg) :
    (applyTerm p (sem ctx) cfg (n+30) 27 444 [.ty (.int w), .reg a, .reg b, .reg c]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRRR .mSub sz (st.fresh .int).1 a b c),
          ((tr.push rid).push rule_inst_2701.id).push rule_inst_3182.id)) := by
  have h := fun st tr n => alu_rrrr_run hp ctx hc st tr n hsz (k := 1) rfl hs
  cases hp
  isel_eval [*, rule_inst_3182]

include hp hc in
/-- `smulh I64 x y` (`(alu_rrr (ALUOp.SMulH) ty x y)`). -/
theorem smulh_run (a b : Reg) :
    (applyTerm p (sem ctx) cfg (n+30) 27 452 [.ty (.int 64), .reg a, .reg b]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRR .sMulH .size64 (st.fresh .int).1 a b),
          ((tr.push rule_inst_1593.id).push rule_inst_2545.id).push rule_inst_3218.id)) := by
  have h := fun st tr n => alu_rrr_run hp ctx hc st tr n
    (fun st tr n => operand_size_64 hp ctx hc st tr n (by decide) (Nat.le_refl 64))
    (fun st rd rn rm => emit_aluRRR ctx st (k := 11) (sz := .size64) (op := .sMulH) rfl rfl rd rn rm)
  cases hp
  isel_eval [*, rule_inst_3218]

include hp hc in
/-- `umulh I64 x y` (`(alu_rrr (ALUOp.UMulH) ty x y)`). -/
theorem umulh_run (a b : Reg) :
    (applyTerm p (sem ctx) cfg (n+30) 27 451 [.ty (.int 64), .reg a, .reg b]).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRR .uMulH .size64 (st.fresh .int).1 a b),
          ((tr.push rule_inst_1593.id).push rule_inst_2545.id).push rule_inst_3213.id)) := by
  have h := fun st tr n => alu_rrr_run hp ctx hc st tr n
    (fun st tr n => operand_size_64 hp ctx hc st tr n (by decide) (Nat.le_refl 64))
    (fun st rd rn rm => emit_aluRRR ctx st (k := 12) (sz := .size64) (op := .uMulH) rfl rfl rd rn rm)
  cases hp
  isel_eval [*, rule_inst_3213]

end Helpers

/-! ## `smulhi_64` (1056), `umulhi_64` (1068) -/

section MulHi
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp in
theorem match_1056 {i x y : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int 64))
    (hd : info.data = .data 152 2 [.data 151 79 [], .values [x, y]]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1056 [.inst i]).run (st, tr) =
      .ok (some (env2a (.value x) (.value y)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have he := sem_eq_beq_fa ctx
  cases hp
  isel_eval [*, rule_lower_1056, ext_value_array_2]

include hp in
theorem match_1056_ne {i x y w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≠ 64)
    (hd : info.data = .data 152 2 [.data 151 79 [], .values [x, y]]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1056 [.inst i]).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have he := sem_eq_beq_fa ctx
  have hne : (V.ty (.int w) == V.ty (.int 64)) = false := by simp [hw]
  cases hp
  isel_eval [*, rule_lower_1056]

include hp hc in
theorem rhs_1056 {x y : Nat} {rx ry : Reg} (hx : ctx.valueReg? x = some rx)
    (hy : ctx.valueReg? y = some ry) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_1056.rhs (env2a (.value x) (.value y))).run
        (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRR .sMulH .size64 (st.fresh .int).1 rx ry), tr')) := by
  have h1 := fun st tr n => smulh_run hp ctx hc st tr n
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_1056, ctor_put_in_reg ctx _ hx, ctor_put_in_reg ctx _ hy]
    rfl

include hp in
theorem rhs_1056_none {x y : Nat} (hxy : ctx.valueReg? x = none ∨ ctx.valueReg? y = none)
    (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_1056.rhs (env2a (.value x) (.value y))).run
      (st, tr) ≠ .ok (some v, s') := by
  cases hp
  rcases hxy with hx | hy
  · isel_eval [*, rule_lower_1056, ctor_put_in_reg_none ctx _ hx]
    exact fun h => by cases h
  · cases hx : ctx.valueReg? x with
    | none =>
      isel_eval [*, rule_lower_1056, ctor_put_in_reg_none ctx _ hx]
      exact fun h => by cases h
    | some rx =>
      isel_eval [*, rule_lower_1056, ctor_put_in_reg ctx _ hx, ctor_put_in_reg_none ctx _ hy]
      exact fun h => by cases h

include hp in
theorem match_1068 {i x y : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int 64))
    (hd : info.data = .data 152 2 [.data 151 78 [], .values [x, y]]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1068 [.inst i]).run (st, tr) =
      .ok (some (env2a (.value x) (.value y)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have he := sem_eq_beq_fa ctx
  cases hp
  isel_eval [*, rule_lower_1068, ext_value_array_2]

include hp in
theorem match_1068_ne {i x y w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≠ 64)
    (hd : info.data = .data 152 2 [.data 151 78 [], .values [x, y]]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_1068 [.inst i]).run (st, tr) =
      .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have he := sem_eq_beq_fa ctx
  have hne : (V.ty (.int w) == V.ty (.int 64)) = false := by simp [hw]
  cases hp
  isel_eval [*, rule_lower_1068]

include hp hc in
theorem rhs_1068 {x y : Nat} {rx ry : Reg} (hx : ctx.valueReg? x = some rx)
    (hy : ctx.valueReg? y = some ry) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_1068.rhs (env2a (.value x) (.value y))).run
        (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRR .uMulH .size64 (st.fresh .int).1 rx ry), tr')) := by
  have h1 := fun st tr n => umulh_run hp ctx hc st tr n
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_1068, ctor_put_in_reg ctx _ hx, ctor_put_in_reg ctx _ hy]
    rfl

include hp in
theorem rhs_1068_none {x y : Nat} (hxy : ctx.valueReg? x = none ∨ ctx.valueReg? y = none)
    (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_1068.rhs (env2a (.value x) (.value y))).run
      (st, tr) ≠ .ok (some v, s') := by
  cases hp
  rcases hxy with hx | hy
  · isel_eval [*, rule_lower_1068, ctor_put_in_reg_none ctx _ hx]
    exact fun h => by cases h
  · cases hx : ctx.valueReg? x with
    | none =>
      isel_eval [*, rule_lower_1068, ctor_put_in_reg_none ctx _ hx]
      exact fun h => by cases h
    | some rx =>
      isel_eval [*, rule_lower_1068, ctor_put_in_reg ctx _ hx, ctor_put_in_reg_none ctx _ hy]
      exact fun h => by cases h

end MulHi

/-! ## `imul_base_case` (871) and the multiply-add fusions (125, 128, 132) -/

section Madd
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp in
theorem match_871 {i x y w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 77 [], .values [x, y]]) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_871 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.value x) (.value y)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  cases hp
  isel_eval [*, rule_lower_871, ext_ty_int_ref_scalar_64_extract ctx st hw, ext_value_array_2]

include hp hc in
theorem rhs_871 {x y w : Nat} {rx ry : Reg} (hx : ctx.valueReg? x = some rx)
    (hy : ctx.valueReg? y = some ry) (hw : w ≤ 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_871.rhs
        (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRRR .mAdd (szOf w) (st.fresh .int).1 rx ry .xzr), tr')) := by
  obtain ⟨ks, rid, hs, hsz⟩ := operand_size_run hp ctx hc hw
  have h1 := fun st tr n => madd_run hp ctx hc st tr n hsz hs
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_871, ctor_put_in_reg ctx _ hx, ctor_put_in_reg ctx _ hy,
      ctor_zero_reg_fa]
    rfl

include hp in
theorem rhs_871_none {x y w : Nat} (hxy : ctx.valueReg? x = none ∨ ctx.valueReg? y = none)
    (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_871.rhs
        (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) ≠ .ok (some v, s') := by
  cases hp
  rcases hxy with hx | hy
  · isel_eval [*, rule_lower_871, ctor_put_in_reg_none ctx _ hx]
    exact fun h => by cases h
  · cases hx : ctx.valueReg? x with
    | none =>
      isel_eval [*, rule_lower_871, ctor_put_in_reg_none ctx _ hx]
      exact fun h => by cases h
    | some rx =>
      isel_eval [*, rule_lower_871, ctor_put_in_reg ctx _ hx, ctor_put_in_reg_none ctx _ hy]
      exact fun h => by cases h

include hp in
theorem match_125 {i x y a b w j : Nat} {info infoj : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 73 [], .values [x, y]])
    (hj : ctx.defInst? y = some j) (hij : ctx.insts[j]? = some infoj)
    (hdj : infoj.data = .data 152 2 [.data 151 77 [], .values [a, b]]) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_125 [.inst i]).run (st, tr) =
      .ok (some (env4 (.ty (.int w)) (.value x) (.value a) (.value b)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_inst_data_value ctx st hij
  rw [hdj] at h2
  have h3 := ext_def_inst_some ctx st hj
  cases hp
  isel_eval [*, rule_lower_125, ext_ty_int_ref_scalar_64_extract ctx st hw, ext_value_array_2]

include hp in
theorem match_128 {i x y a b w j : Nat} {info infoj : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 73 [], .values [x, y]])
    (hj : ctx.defInst? x = some j) (hij : ctx.insts[j]? = some infoj)
    (hdj : infoj.data = .data 152 2 [.data 151 77 [], .values [a, b]]) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_128 [.inst i]).run (st, tr) =
      .ok (some (env4 (.ty (.int w)) (.value a) (.value b) (.value y)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_inst_data_value ctx st hij
  rw [hdj] at h2
  have h3 := ext_def_inst_some ctx st hj
  cases hp
  isel_eval [*, rule_lower_128, ext_ty_int_ref_scalar_64_extract ctx st hw, ext_value_array_2]

include hp in
theorem match_132 {i x y a b w j : Nat} {info infoj : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 74 [], .values [x, y]])
    (hj : ctx.defInst? y = some j) (hij : ctx.insts[j]? = some infoj)
    (hdj : infoj.data = .data 152 2 [.data 151 77 [], .values [a, b]]) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_132 [.inst i]).run (st, tr) =
      .ok (some (env4 (.ty (.int w)) (.value x) (.value a) (.value b)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_inst_data_value ctx st hij
  rw [hdj] at h2
  have h3 := ext_def_inst_some ctx st hj
  cases hp
  isel_eval [*, rule_lower_132, ext_ty_int_ref_scalar_64_extract ctx st hw, ext_value_array_2]

include hp hc in
theorem rhs_125 {x a b w : Nat} {rx ra rb : Reg} (hx : ctx.valueReg? x = some rx)
    (ha : ctx.valueReg? a = some ra) (hb : ctx.valueReg? b = some rb) (hw : w ≤ 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_125.rhs
        (env4 (.ty (.int w)) (.value x) (.value a) (.value b))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRRR .mAdd (szOf w) (st.fresh .int).1 ra rb rx), tr')) := by
  obtain ⟨ks, rid, hs, hsz⟩ := operand_size_run hp ctx hc hw
  have h1 := fun st tr n => madd_run hp ctx hc st tr n hsz hs
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_125, ctor_put_in_reg ctx _ hx, ctor_put_in_reg ctx _ ha,
      ctor_put_in_reg ctx _ hb]
    rfl

include hp hc in
theorem rhs_128 {a b y w : Nat} {ra rb ry : Reg} (ha : ctx.valueReg? a = some ra)
    (hb : ctx.valueReg? b = some rb) (hy : ctx.valueReg? y = some ry) (hw : w ≤ 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_128.rhs
        (env4 (.ty (.int w)) (.value a) (.value b) (.value y))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRRR .mAdd (szOf w) (st.fresh .int).1 ra rb ry), tr')) := by
  obtain ⟨ks, rid, hs, hsz⟩ := operand_size_run hp ctx hc hw
  have h1 := fun st tr n => madd_run hp ctx hc st tr n hsz hs
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_128, ctor_put_in_reg ctx _ hy, ctor_put_in_reg ctx _ ha,
      ctor_put_in_reg ctx _ hb]
    rfl

include hp hc in
theorem rhs_132 {x a b w : Nat} {rx ra rb : Reg} (hx : ctx.valueReg? x = some rx)
    (ha : ctx.valueReg? a = some ra) (hb : ctx.valueReg? b = some rb) (hw : w ≤ 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_132.rhs
        (env4 (.ty (.int w)) (.value x) (.value a) (.value b))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRRR .mSub (szOf w) (st.fresh .int).1 ra rb rx), tr')) := by
  obtain ⟨ks, rid, hs, hsz⟩ := operand_size_run hp ctx hc hw
  have h1 := fun st tr n => msub_run hp ctx hc st tr n hsz hs
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_132, ctor_put_in_reg ctx _ hx, ctor_put_in_reg ctx _ ha,
      ctor_put_in_reg ctx _ hb]
    rfl

/-- The three-register right-hand sides fail when an operand has no register. -/
theorem valueReg3_cases {a b c : Nat} :
    (∃ ra rb rc, ctx.valueReg? a = some ra ∧ ctx.valueReg? b = some rb ∧ ctx.valueReg? c = some rc) ∨
      ctx.valueReg? a = none ∨ (ctx.valueReg? a).isSome ∧ ctx.valueReg? b = none ∨
      (ctx.valueReg? a).isSome ∧ (ctx.valueReg? b).isSome ∧ ctx.valueReg? c = none := by
  cases ha : ctx.valueReg? a <;> cases hb : ctx.valueReg? b <;> cases hc : ctx.valueReg? c <;> simp

include hp in
theorem rhs_125_none {x a b w : Nat}
    (h : ctx.valueReg? x = none ∨ ctx.valueReg? a = none ∨ ctx.valueReg? b = none)
    (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_125.rhs
        (env4 (.ty (.int w)) (.value x) (.value a) (.value b))).run (st, tr) ≠ .ok (some v, s') := by
  cases hp
  cases ha : ctx.valueReg? a with
  | none =>
    isel_eval [*, rule_lower_125, ctor_put_in_reg_none ctx _ ha]
    exact fun h => by cases h
  | some ra =>
  cases hb : ctx.valueReg? b with
  | none =>
    isel_eval [*, rule_lower_125, ctor_put_in_reg ctx _ ha, ctor_put_in_reg_none ctx _ hb]
    exact fun h => by cases h
  | some rb =>
  have hx : ctx.valueReg? x = none := by simpa [ha, hb] using h
  isel_eval [*, rule_lower_125, ctor_put_in_reg ctx _ ha, ctor_put_in_reg ctx _ hb,
    ctor_put_in_reg_none ctx _ hx]
  exact fun h => by cases h

include hp in
theorem rhs_128_none {a b y w : Nat}
    (h : ctx.valueReg? a = none ∨ ctx.valueReg? b = none ∨ ctx.valueReg? y = none)
    (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_128.rhs
        (env4 (.ty (.int w)) (.value a) (.value b) (.value y))).run (st, tr) ≠ .ok (some v, s') := by
  cases hp
  cases ha : ctx.valueReg? a with
  | none =>
    isel_eval [*, rule_lower_128, ctor_put_in_reg_none ctx _ ha]
    exact fun h => by cases h
  | some ra =>
  cases hb : ctx.valueReg? b with
  | none =>
    isel_eval [*, rule_lower_128, ctor_put_in_reg ctx _ ha, ctor_put_in_reg_none ctx _ hb]
    exact fun h => by cases h
  | some rb =>
  have hy : ctx.valueReg? y = none := by simpa [ha, hb] using h
  isel_eval [*, rule_lower_128, ctor_put_in_reg ctx _ ha, ctor_put_in_reg ctx _ hb,
    ctor_put_in_reg_none ctx _ hy]
  exact fun h => by cases h

include hp in
theorem rhs_132_none {x a b w : Nat}
    (h : ctx.valueReg? x = none ∨ ctx.valueReg? a = none ∨ ctx.valueReg? b = none)
    (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_132.rhs
        (env4 (.ty (.int w)) (.value x) (.value a) (.value b))).run (st, tr) ≠ .ok (some v, s') := by
  cases hp
  cases ha : ctx.valueReg? a with
  | none =>
    isel_eval [*, rule_lower_132, ctor_put_in_reg_none ctx _ ha]
    exact fun h => by cases h
  | some ra =>
  cases hb : ctx.valueReg? b with
  | none =>
    isel_eval [*, rule_lower_132, ctor_put_in_reg ctx _ ha, ctor_put_in_reg_none ctx _ hb]
    exact fun h => by cases h
  | some rb =>
  have hx : ctx.valueReg? x = none := by simpa [ha, hb] using h
  isel_eval [*, rule_lower_132, ctor_put_in_reg ctx _ ha, ctor_put_in_reg ctx _ hb,
    ctor_put_in_reg_none ctx _ hx]
  exact fun h => by cases h

end Madd

end Backend.Proof
