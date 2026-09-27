import FV.Backend.Proof.IselTermsLogic

/-!
# `alu_rs_imm_logic` (term 566) and the `band`/`bor`/`bxor`-with-`bnot` root rules: forward
lemmas

`alu_rs_imm_logic op ty x y` (`inst.isle:3937`, three rules) is the non-commutative variant of
`alu_rs_imm_logic_commutative`: `AluRRR op` (rule 3939), `AluRRImmLogic op` when `y` is an
`iconst` encodable as a logical immediate (3941), `AluRRRShift op … lsl #amt` when `y` is
`ishl z (iconst k)` (3944). Its rules have the shapes of 3916/3920/3928, so the forward lemmas
here are theirs with the rule replaced. The root rules `band/bor/bxor x (bnot y)` (1429, 1466,
1534) and their mirrors (1431, 1468, 1536) call it with `AndNot`/`OrrNot`/`EorNot`.
`IselFamALUALogicNot` assembles the term contract and the rule theorems.
-/

namespace Backend.Proof

open Isle Isle.Interp Isle.Aarch64

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

/-! ## The three rules of `alu_rs_imm_logic` -/

section Rules
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp in
theorem match_3939 (k w x y : Nat) :
    (matchRule p (sem ctx) cfg (n+2) rule_inst_3939 [.data 59 k [], .ty (.int w), .value x, .value y]).run
      (st, tr) =
      .ok (some (env4 (.data 59 k []) (.ty (.int w)) (.value x) (.value y)), (st, tr)) := by
  cases hp
  isel_eval [rule_inst_3939]

include hp hc in
theorem rhs_3939 {k w x y : Nat} {op : ALUOp} {rx ry : Reg} (hk : ALUOp.ofIdx? k = some op)
    (hx : ctx.valueReg? x = some rx) (hy : ctx.valueReg? y = some ry) (hw : w ≤ 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_inst_3939.rhs
        (env4 (.data 59 k []) (.ty (.int w)) (.value x) (.value y))).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRR op (szOf w) (st.fresh .int).1 rx ry), tr')) := by
  obtain ⟨ks, rid, hs, hsz⟩ := operand_size_run hp ctx hc hw
  have h1 := fun st tr n => alu_rrr_run hp ctx hc st tr n hsz
    (fun st rd rn rm => emit_aluRRR ctx st hk hs rd rn rm)
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_inst_3939, ctor_put_in_reg ctx _ hx, ctor_put_in_reg ctx _ hy]
    rfl

include hp in
theorem rhs_3939_none {k w x y : Nat} (hxy : ctx.valueReg? x = none ∨ ctx.valueReg? y = none)
    (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_inst_3939.rhs
        (env4 (.data 59 k []) (.ty (.int w)) (.value x) (.value y))).run (st, tr) ≠ .ok (some v, s') := by
  cases hp
  rcases hxy with hx | hy
  · isel_eval [*, rule_inst_3939, ctor_put_in_reg_none ctx _ hx]
    exact fun h => by cases h
  · cases hx : ctx.valueReg? x with
    | none =>
      isel_eval [*, rule_inst_3939, ctor_put_in_reg_none ctx _ hx]
      exact fun h => by cases h
    | some rx =>
      isel_eval [*, rule_inst_3939, ctor_put_in_reg ctx _ hx, ctor_put_in_reg_none ctx _ hy]
      exact fun h => by cases h

include hp in
theorem match_3941 {k w x y j : Nat} {kk : Int} {infoj : IInfo} {imm : ImmLogic}
    (hj : ctx.defInst? y = some j) (hij : ctx.insts[j]? = some infoj)
    (hdj : infoj.data = .data 152 35 [.data 151 57 [], .int kk]) (himm : immLogicOf? w kk = some imm) :
    (matchRule p (sem ctx) cfg (n+10) rule_inst_3941 [.data 59 k [], .ty (.int w), .value x, .value y]).run
      (st, tr) =
      .ok (some (env5 (.data 59 k []) (.ty (.int w)) (.value x) (.int kk) (.op (.immLogic imm))),
        (st, tr)) := by
  have h2 := ext_inst_data_value ctx st hij
  rw [hdj] at h2
  have h3 := ext_def_inst_some ctx st hj
  have h4 := ctor_imm_logic_some ctx st himm
  cases hp
  isel_eval [*, rule_inst_3941]

include hp in
theorem match_3941_none {k w x y j : Nat} {kk : Int} {infoj : IInfo}
    (hj : ctx.defInst? y = some j) (hij : ctx.insts[j]? = some infoj)
    (hdj : infoj.data = .data 152 35 [.data 151 57 [], .int kk]) (himm : immLogicOf? w kk = none) :
    (matchRule p (sem ctx) cfg (n+10) rule_inst_3941 [.data 59 k [], .ty (.int w), .value x, .value y]).run
      (st, tr) = .ok (none, (st, tr)) := by
  have h2 := ext_inst_data_value ctx st hij
  rw [hdj] at h2
  have h3 := ext_def_inst_some ctx st hj
  have h4 := ctor_imm_logic_none ctx st himm
  cases hp
  isel_eval [*, rule_inst_3941]

include hp hc in
theorem rhs_3941 {k w x : Nat} {kk : Int} {op : ALUOp} {rx : Reg} {imm : ImmLogic}
    (hk : ALUOp.ofIdx? k = some op) (hx : ctx.valueReg? x = some rx) (hw : w ≤ 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_inst_3941.rhs
        (env5 (.data 59 k []) (.ty (.int w)) (.value x) (.int kk) (.op (.immLogic imm)))).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRImmLogic op (szOf w) (st.fresh .int).1 rx imm), tr')) := by
  obtain ⟨ks, rid, hs, hsz⟩ := operand_size_run hp ctx hc hw
  have h1 := fun st tr n => alu_rr_imm_logic_run hp ctx hc st tr n hsz hk hs
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_inst_3941, ctor_put_in_reg ctx _ hx]
    rfl

include hp in
theorem rhs_3941_none {k w x : Nat} {kk : Int} {imm : ImmLogic} (hx : ctx.valueReg? x = none)
    (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_inst_3941.rhs
        (env5 (.data 59 k []) (.ty (.int w)) (.value x) (.int kk) (.op (.immLogic imm)))).run (st, tr) ≠
      .ok (some v, s') := by
  cases hp
  isel_eval [*, rule_inst_3941, ctor_put_in_reg_none ctx _ hx]
  exact fun h => by cases h

include hp in
theorem match_3944 {k w x y z b j1 j2 : Nat} {kk : Int} {info1 info2 : IInfo} {sh : ShiftOpAndAmt}
    (hj1 : ctx.defInst? y = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hd1 : info1.data = .data 152 2 [.data 151 103 [], .values [z, b]])
    (hj2 : ctx.defInst? b = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hd2 : info2.data = .data 152 35 [.data 151 57 [], .int kk]) (hsh : lshlOf? w kk = some sh) :
    (matchRule p (sem ctx) cfg (n+10) rule_inst_3944 [.data 59 k [], .ty (.int w), .value x, .value y]).run
      (st, tr) =
      .ok (some (env6 (.data 59 k []) (.ty (.int w)) (.value x) (.value z) (.int kk)
        (.op (.shiftOpAndAmt sh))), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hij1
  rw [hd1] at h1
  have h2 := ext_inst_data_value ctx st hij2
  rw [hd2] at h2
  have h3 := ext_def_inst_some ctx st hj1
  have h3' := ext_def_inst_some ctx st hj2
  have h4 := ctor_lshl_some ctx st hsh
  cases hp
  isel_eval [*, rule_inst_3944, ext_value_array_2]

include hp in
theorem match_3944_none {k w x y z b j1 j2 : Nat} {kk : Int} {info1 info2 : IInfo}
    (hj1 : ctx.defInst? y = some j1) (hij1 : ctx.insts[j1]? = some info1)
    (hd1 : info1.data = .data 152 2 [.data 151 103 [], .values [z, b]])
    (hj2 : ctx.defInst? b = some j2) (hij2 : ctx.insts[j2]? = some info2)
    (hd2 : info2.data = .data 152 35 [.data 151 57 [], .int kk]) (hsh : lshlOf? w kk = none) :
    (matchRule p (sem ctx) cfg (n+10) rule_inst_3944 [.data 59 k [], .ty (.int w), .value x, .value y]).run
      (st, tr) = .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hij1
  rw [hd1] at h1
  have h2 := ext_inst_data_value ctx st hij2
  rw [hd2] at h2
  have h3 := ext_def_inst_some ctx st hj1
  have h3' := ext_def_inst_some ctx st hj2
  have h4 := ctor_lshl_none ctx st hsh
  cases hp
  isel_eval [*, rule_inst_3944, ext_value_array_2]

include hp hc in
theorem rhs_3944 {k w x z : Nat} {kk : Int} {op : ALUOp} {rx rz : Reg} {sh : ShiftOpAndAmt}
    (hk : ALUOp.ofIdx? k = some op) (hx : ctx.valueReg? x = some rx) (hz : ctx.valueReg? z = some rz)
    (hw : w ≤ 64) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_inst_3944.rhs
        (env6 (.data 59 k []) (.ty (.int w)) (.value x) (.value z) (.int kk)
          (.op (.shiftOpAndAmt sh)))).run (st, tr) =
      .ok (some (.reg (st.fresh .int).1),
        ((st.fresh .int).2.emit (.aluRRRShift op (szOf w) (st.fresh .int).1 rx rz sh), tr')) := by
  obtain ⟨ks, rid, hs, hsz⟩ := operand_size_run hp ctx hc hw
  have h1 := fun st tr n => alu_rrr_shift_run hp ctx hc st tr n hsz hk hs
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_inst_3944, ctor_put_in_reg ctx _ hx, ctor_put_in_reg ctx _ hz]
    rfl

include hp in
theorem rhs_3944_none {k w x z : Nat} {kk : Int} {sh : ShiftOpAndAmt}
    (hxz : ctx.valueReg? x = none ∨ ctx.valueReg? z = none) (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_inst_3944.rhs
        (env6 (.data 59 k []) (.ty (.int w)) (.value x) (.value z) (.int kk)
          (.op (.shiftOpAndAmt sh)))).run (st, tr) ≠ .ok (some v, s') := by
  cases hp
  rcases hxz with hx | hz
  · isel_eval [*, rule_inst_3944, ctor_put_in_reg_none ctx _ hx]
    exact fun h => by cases h
  · cases hx : ctx.valueReg? x with
    | none =>
      isel_eval [*, rule_inst_3944, ctor_put_in_reg_none ctx _ hx]
      exact fun h => by cases h
    | some rx =>
      isel_eval [*, rule_inst_3944, ctor_put_in_reg ctx _ hx, ctor_put_in_reg_none ctx _ hz]
      exact fun h => by cases h

end Rules

/-! ## The root rules `cop x (bnot y)` (1429, 1466, 1534) and `cop (bnot y) x` (1431, 1468,
1536): match phase and the arguments of `alu_rs_imm_logic` -/

section Roots
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp in
theorem match_1429 {i x y y' w j : Nat} {info infoj : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 97 [], .values [x, y]])
    (hj : ctx.defInst? y = some j) (hij : ctx.insts[j]? = some infoj)
    (hdj : infoj.data = .data 152 29 [.data 151 100 [], .value y']) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_1429 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.value x) (.value y')), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_64 ctx st w
  simp only [hw, ↓reduceIte] at h2
  have h3 := ext_inst_data_value ctx st hij
  rw [hdj] at h3
  have h4 := ext_def_inst_some ctx st hj
  cases hp
  isel_eval [*, rule_lower_1429, ext_ty_int, ext_value_array_2]

include hp in
theorem match_1431 {i x y y' w j : Nat} {info infoj : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 97 [], .values [y, x]])
    (hj : ctx.defInst? y = some j) (hij : ctx.insts[j]? = some infoj)
    (hdj : infoj.data = .data 152 29 [.data 151 100 [], .value y']) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_1431 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.value y') (.value x)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_64 ctx st w
  simp only [hw, ↓reduceIte] at h2
  have h3 := ext_inst_data_value ctx st hij
  rw [hdj] at h3
  have h4 := ext_def_inst_some ctx st hj
  cases hp
  isel_eval [*, rule_lower_1431, ext_ty_int, ext_value_array_2]

include hp in
theorem match_1466 {i x y y' w j : Nat} {info infoj : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 98 [], .values [x, y]])
    (hj : ctx.defInst? y = some j) (hij : ctx.insts[j]? = some infoj)
    (hdj : infoj.data = .data 152 29 [.data 151 100 [], .value y']) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_1466 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.value x) (.value y')), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_64 ctx st w
  simp only [hw, ↓reduceIte] at h2
  have h3 := ext_inst_data_value ctx st hij
  rw [hdj] at h3
  have h4 := ext_def_inst_some ctx st hj
  cases hp
  isel_eval [*, rule_lower_1466, ext_ty_int, ext_value_array_2]

include hp in
theorem match_1468 {i x y y' w j : Nat} {info infoj : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 98 [], .values [y, x]])
    (hj : ctx.defInst? y = some j) (hij : ctx.insts[j]? = some infoj)
    (hdj : infoj.data = .data 152 29 [.data 151 100 [], .value y']) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_1468 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.value y') (.value x)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_64 ctx st w
  simp only [hw, ↓reduceIte] at h2
  have h3 := ext_inst_data_value ctx st hij
  rw [hdj] at h3
  have h4 := ext_def_inst_some ctx st hj
  cases hp
  isel_eval [*, rule_lower_1468, ext_ty_int, ext_value_array_2]

include hp in
theorem match_1534 {i x y y' w j : Nat} {info infoj : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 99 [], .values [x, y]])
    (hj : ctx.defInst? y = some j) (hij : ctx.insts[j]? = some infoj)
    (hdj : infoj.data = .data 152 29 [.data 151 100 [], .value y']) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_1534 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.value x) (.value y')), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_64 ctx st w
  simp only [hw, ↓reduceIte] at h2
  have h3 := ext_inst_data_value ctx st hij
  rw [hdj] at h3
  have h4 := ext_def_inst_some ctx st hj
  cases hp
  isel_eval [*, rule_lower_1534, ext_ty_int, ext_value_array_2]

include hp in
theorem match_1536 {i x y y' w j : Nat} {info infoj : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 99 [], .values [y, x]])
    (hj : ctx.defInst? y = some j) (hij : ctx.insts[j]? = some infoj)
    (hdj : infoj.data = .data 152 29 [.data 151 100 [], .value y']) :
    (matchRule p (sem ctx) cfg (n+10) rule_lower_1536 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.value y') (.value x)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_fits_in_64 ctx st w
  simp only [hw, ↓reduceIte] at h2
  have h3 := ext_inst_data_value ctx st hij
  rw [hdj] at h3
  have h4 := ext_def_inst_some ctx st hj
  cases hp
  isel_eval [*, rule_lower_1536, ext_ty_int, ext_value_array_2]

include hp in
/-- The arguments of `alu_rs_imm_logic` in the rules `cop x (bnot y)`: `(op ty x y)`. -/
theorem args_not_right (opT k w a b : Nat) (hk : ∀ (st : LState) (tr : Array RuleId) n,
      (evalExpr p (sem ctx) cfg (n+2) (.term 59 opT []) (env3 (.ty (.int w)) (.value a) (.value b))).run
        (st, tr) = .ok (some (.data 59 k []), (st, tr))) :
    (evalArgs p (sem ctx) cfg (n+5) [.term 59 opT [], .var 14 0, .var 15 1, .var 15 2]
      (env3 (.ty (.int w)) (.value a) (.value b))).run (st, tr) =
      .ok (some [.data 59 k [], .ty (.int w), .value a, .value b], (st, tr)) := by
  have h := hk st tr (n+2)
  cases hp
  isel_eval [*]

include hp in
/-- The arguments of `alu_rs_imm_logic` in the rules `cop (bnot y) x`: `(op ty x y)` from the
environment `[ty, y, x]`. -/
theorem args_not_left (opT k w a b : Nat) (hk : ∀ (st : LState) (tr : Array RuleId) n,
      (evalExpr p (sem ctx) cfg (n+2) (.term 59 opT []) (env3 (.ty (.int w)) (.value a) (.value b))).run
        (st, tr) = .ok (some (.data 59 k []), (st, tr))) :
    (evalArgs p (sem ctx) cfg (n+5) [.term 59 opT [], .var 14 0, .var 15 2, .var 15 1]
      (env3 (.ty (.int w)) (.value a) (.value b))).run (st, tr) =
      .ok (some [.data 59 k [], .ty (.int w), .value b, .value a], (st, tr)) := by
  have h := hk st tr (n+2)
  cases hp
  isel_eval [*]

include hp in
theorem enum_AndNot (w a b : Nat) (st : LState) (tr : Array RuleId) (n : Nat) :
    (evalExpr p (sem ctx) cfg (n+2) (.term 59 1968 []) (env3 (.ty (.int w)) (.value a) (.value b))).run
      (st, tr) = .ok (some (.data 59 6 []), (st, tr)) := by
  cases hp
  isel_eval [*]

include hp in
theorem enum_OrrNot (w a b : Nat) (st : LState) (tr : Array RuleId) (n : Nat) :
    (evalExpr p (sem ctx) cfg (n+2) (.term 59 1965 []) (env3 (.ty (.int w)) (.value a) (.value b))).run
      (st, tr) = .ok (some (.data 59 3 []), (st, tr)) := by
  cases hp
  isel_eval [*]

include hp in
theorem enum_EorNot (w a b : Nat) (st : LState) (tr : Array RuleId) (n : Nat) :
    (evalExpr p (sem ctx) cfg (n+2) (.term 59 1970 []) (env3 (.ty (.int w)) (.value a) (.value b))).run
      (st, tr) = .ok (some (.data 59 8 []), (st, tr)) := by
  cases hp
  isel_eval [*]

end Roots

end Backend.Proof
