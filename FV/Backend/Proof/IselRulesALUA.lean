import FV.Backend.Proof.IselTermsALUA
import FV.Backend.Proof.IselFamALUA

/-!
# Forward interpreter lemmas for the family-A root rules

For each rule: the match phase on the instruction and the looked-through definitions
(`match_*`), the right-hand side from the environment it builds (`rhs_*`, every width via
`operand_size_run`), and the right-hand side failing when an operand has no register
(`rhs_*_none`). All by `isel_eval` over an abstract `p` with `Data p`; the rule theorems are in
`IselFamALUARules`.
-/

namespace Backend.Proof

open Isle Isle.Interp Isle.Aarch64

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

theorem ext_imm12_from_u64_some (st : LState) {k : Int} {imm : Imm12}
    (h : Imm12.ofNat? (u64 k) = some imm) :
    externExtract ctx T.imm12_from_u64 (.int ((u64 k : Nat) : Int)) st = .ok [.op (.imm12 imm)] := by
  rw [ext_imm12_from_u64, u64_ofNat (u64_lt k), h]

/-! ## `iadd_imm12_right` (`lower.isle:90`) and `iadd_imm12_left` (`:93`), `isub_imm12` (`:805`) -/

include hp in
theorem match_90 {i x y w j : Nat} {k : Int} {info infoj : IInfo} {imm : Imm12}
    (hi : ctx.insts[i]? = some info) (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 73 [], .values [x, y]])
    (hj : ctx.defInst? y = some j) (hij : ctx.insts[j]? = some infoj)
    (hdj : infoj.data = .data 152 35 [.data 151 57 [], .int k])
    (himm : Imm12.ofNat? (u64 k) = some imm) (st : LState) (tr : Array RuleId) (n : Nat) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_90 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.value x) (.op (.imm12 imm))), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_inst_data_value ctx st hij
  rw [hdj] at h2
  have h3 := ext_def_inst_some ctx st hj
  have h4 := ext_imm12_from_u64_some ctx st himm
  cases hp
  isel_eval [*, rule_lower_90, ext_ty_int_ref_scalar_64_extract ctx st hw, ext_value_array_2,
    ext_u64_from_imm64]

include hp hc in
theorem rhs_90 {x w : Nat} {rx : Reg} {imm : Imm12} (hx : ctx.valueReg? x = some rx)
    (hw : w ≤ 64) (st : LState) (tr : Array RuleId) (n : Nat) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_90.rhs
        (env3 (.ty (.int w)) (.value x) (.op (.imm12 imm)))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRImm12 .add (szOf w) (st.fresh .int).1 rx imm), tr')) := by
  obtain ⟨ks, rid, hs, hsz⟩ := operand_size_run hp ctx hc hw
  have h1 := fun st tr n => add_imm_run hp ctx hc st tr n hsz hs
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_90, ctor_put_in_reg ctx _ hx]
    rfl

include hp in
theorem rhs_90_none {x w : Nat} {imm : Imm12} (hx : ctx.valueReg? x = none)
    (st : LState) (tr : Array RuleId) (n : Nat) (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_90.rhs
        (env3 (.ty (.int w)) (.value x) (.op (.imm12 imm)))).run (st, tr) ≠ .ok (some v, s') := by
  cases hp
  isel_eval [*, rule_lower_90, ctor_put_in_reg_none ctx _ hx]
  exact fun h => by cases h

include hp in
theorem match_93 {i x y w j : Nat} {k : Int} {info infoj : IInfo} {imm : Imm12}
    (hi : ctx.insts[i]? = some info) (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 73 [], .values [x, y]])
    (hj : ctx.defInst? x = some j) (hij : ctx.insts[j]? = some infoj)
    (hdj : infoj.data = .data 152 35 [.data 151 57 [], .int k])
    (himm : Imm12.ofNat? (u64 k) = some imm) (st : LState) (tr : Array RuleId) (n : Nat) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_93 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.op (.imm12 imm)) (.value y)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_inst_data_value ctx st hij
  rw [hdj] at h2
  have h3 := ext_def_inst_some ctx st hj
  have h4 := ext_imm12_from_u64_some ctx st himm
  cases hp
  isel_eval [*, rule_lower_93, ext_ty_int_ref_scalar_64_extract ctx st hw, ext_value_array_2,
    ext_u64_from_imm64]

include hp hc in
theorem rhs_93 {y w : Nat} {ry : Reg} {imm : Imm12} (hy : ctx.valueReg? y = some ry)
    (hw : w ≤ 64) (st : LState) (tr : Array RuleId) (n : Nat) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_93.rhs
        (env3 (.ty (.int w)) (.op (.imm12 imm)) (.value y))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRImm12 .add (szOf w) (st.fresh .int).1 ry imm), tr')) := by
  obtain ⟨ks, rid, hs, hsz⟩ := operand_size_run hp ctx hc hw
  have h1 := fun st tr n => add_imm_run hp ctx hc st tr n hsz hs
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_93, ctor_put_in_reg ctx _ hy]
    rfl

include hp in
theorem rhs_93_none {y w : Nat} {imm : Imm12} (hy : ctx.valueReg? y = none)
    (st : LState) (tr : Array RuleId) (n : Nat) (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_93.rhs
        (env3 (.ty (.int w)) (.op (.imm12 imm)) (.value y))).run (st, tr) ≠ .ok (some v, s') := by
  cases hp
  isel_eval [*, rule_lower_93, ctor_put_in_reg_none ctx _ hy]
  exact fun h => by cases h

include hp in
theorem match_805 {i x y w j : Nat} {k : Int} {info infoj : IInfo} {imm : Imm12}
    (hi : ctx.insts[i]? = some info) (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 74 [], .values [x, y]])
    (hj : ctx.defInst? y = some j) (hij : ctx.insts[j]? = some infoj)
    (hdj : infoj.data = .data 152 35 [.data 151 57 [], .int k])
    (himm : Imm12.ofNat? (u64 k) = some imm) (st : LState) (tr : Array RuleId) (n : Nat) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_805 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.value x) (.op (.imm12 imm))), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  have h2 := ext_inst_data_value ctx st hij
  rw [hdj] at h2
  have h3 := ext_def_inst_some ctx st hj
  have h4 := ext_imm12_from_u64_some ctx st himm
  cases hp
  isel_eval [*, rule_lower_805, ext_ty_int_ref_scalar_64_extract ctx st hw, ext_value_array_2,
    ext_u64_from_imm64]

include hp hc in
theorem rhs_805 {x w : Nat} {rx : Reg} {imm : Imm12} (hx : ctx.valueReg? x = some rx)
    (hw : w ≤ 64) (st : LState) (tr : Array RuleId) (n : Nat) :
    ∃ tr', (evalExpr p (sem ctx) cfg (n+40) rule_lower_805.rhs
        (env3 (.ty (.int w)) (.value x) (.op (.imm12 imm)))).run (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRImm12 .sub (szOf w) (st.fresh .int).1 rx imm), tr')) := by
  obtain ⟨ks, rid, hs, hsz⟩ := operand_size_run hp ctx hc hw
  have h1 := fun st tr n => sub_imm_run hp ctx hc st tr n hsz hs
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  cases hp
  refine Exists.intro ?w ?h
  case h =>
    isel_eval [*, rule_lower_805, ctor_put_in_reg ctx _ hx]
    rfl

include hp in
theorem rhs_805_none {x w : Nat} {imm : Imm12} (hx : ctx.valueReg? x = none)
    (st : LState) (tr : Array RuleId) (n : Nat) (v : V) (s' : LState × Array RuleId) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_805.rhs
        (env3 (.ty (.int w)) (.value x) (.op (.imm12 imm)))).run (st, tr) ≠ .ok (some v, s') := by
  cases hp
  isel_eval [*, rule_lower_805, ctor_put_in_reg_none ctx _ hx]
  exact fun h => by cases h

/-! ## `imm12_from_negated_value` and the negated-immediate rules (98, 102, 810) -/

/-- What `imm12_from_negated_value` computes from an `iconst` of width `w` and immediate `k`:
the `Imm12` of `-(sign-extended k)` as an unsigned 64-bit number, if the negation does not
overflow. -/
def negImm12? (w : Nat) (k : Int) : Option Imm12 :=
  if sextFrom w k = -(2 ^ 63 : Int) then none
  else Imm12.ofNat? (u64 ((u64 (-(sextFrom w k)) : Nat) : Int))

/-- A four-variable rule environment as the matcher builds it. -/
abbrev env4 (a b c d : V) : Interp.Env V :=
  ((((Array.replicate 4 none).setIfInBounds 0 (some a)).setIfInBounds 1 (some b)).setIfInBounds 2
    (some c)).setIfInBounds 3 (some d)

section Neg
variable (st : LState)

theorem ctor_i64_sextend_imm64 (w : Nat) (k : Int) :
    externCtor ctx T.i64_sextend_imm64 [.ty (.int w), .int k] st = .ok (.int (sextFrom w k), st) :=
  rfl

theorem ctor_i64_checked_neg_ok {a : Int} (h : a ≠ -(2 ^ 63 : Int)) :
    externCtor ctx T.i64_checked_neg [.int a] st = .ok (.int (-a), st) := by
  show (if a == -(2 ^ 63 : Int) then ExtResult.fail else .ok (V.int (-a), st)) = _
  rw [beq_false_of_ne h]
  rfl

theorem ctor_i64_checked_neg_fail {a : Int} (h : a = -(2 ^ 63 : Int)) :
    externCtor ctx T.i64_checked_neg [.int a] st = .fail := by
  show (if a == -(2 ^ 63 : Int) then ExtResult.fail else .ok (V.int (-a), st)) = _
  rw [beq_iff_eq.mpr h]
  rfl

theorem ctor_i64_cast_unsigned (a : Int) :
    externCtor ctx T.i64_cast_unsigned [.int a] st = .ok (.int (u64 a), st) := rfl

theorem ext_imm12_from_u64_of {i : Int} {imm : Imm12} (h : Imm12.ofNat? (u64 i) = some imm) :
    externExtract ctx T.imm12_from_u64 (.int i) st = .ok [.op (.imm12 imm)] := by
  rw [ext_imm12_from_u64, h]

theorem ext_imm12_from_u64_none {i : Int} (h : Imm12.ofNat? (u64 i) = none) :
    externExtract ctx T.imm12_from_u64 (.int i) st = .fail := by
  rw [ext_imm12_from_u64, h]

end Neg

section NegRun
variable (st : LState) (tr : Array RuleId) (n : Nat)

include hp hc in
theorem imm12_from_negated_value_some {y j w : Nat} {k : Int} {infoj : IInfo} {imm : Imm12}
    (hj : ctx.defInst? y = some j) (hij : ctx.insts[j]? = some infoj)
    (hty : infoj.resTys.head? = some (.int w))
    (hdj : infoj.data = .data 152 35 [.data 151 57 [], .int k]) (h : negImm12? w k = some imm) :
    (applyTerm p (sem ctx) cfg (n+30) 64 344 [.value y]).run (st, tr) =
      .ok (some (.op (.imm12 imm)), (st, tr.push rule_inst_2404.id)) := by
  have h1 := ext_inst_data_value ctx st hij
  rw [hdj, hty, Option.getD_some] at h1
  have h3 := ext_def_inst_some ctx st hj
  unfold negImm12? at h
  split at h
  · cases h
  · rename_i hn
    have h4 := ctor_i64_checked_neg_ok ctx st hn
    have h5 := ext_imm12_from_u64_of ctx st h
    clear hn h
    cases hp
    isel_eval [*, rule_inst_2404, ctor_i64_sextend_imm64, ctor_i64_cast_unsigned]

include hp hc in
theorem imm12_from_negated_value_none {y j w : Nat} {k : Int} {infoj : IInfo}
    (hj : ctx.defInst? y = some j) (hij : ctx.insts[j]? = some infoj)
    (hty : infoj.resTys.head? = some (.int w))
    (hdj : infoj.data = .data 152 35 [.data 151 57 [], .int k]) (h : negImm12? w k = none) :
    (applyTerm p (sem ctx) cfg (n+30) 64 344 [.value y]).run (st, tr) = .ok (none, (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hij
  rw [hdj, hty, Option.getD_some] at h1
  have h3 := ext_def_inst_some ctx st hj
  unfold negImm12? at h
  split at h
  · rename_i hn
    have h4 := ctor_i64_checked_neg_fail ctx st hn
    clear hn h
    cases hp
    isel_eval [*, rule_inst_2404, ctor_i64_sextend_imm64, ctor_i64_cast_unsigned]
  · have h5 := ext_imm12_from_u64_none ctx st h
    rename_i hn
    have h4 := ctor_i64_checked_neg_ok ctx st hn
    clear hn h
    cases hp
    isel_eval [*, rule_inst_2404, ctor_i64_sextend_imm64, ctor_i64_cast_unsigned]

end NegRun

end Backend.Proof
