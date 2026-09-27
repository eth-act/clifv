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

end Backend.Proof
