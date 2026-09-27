import FV.Backend.Proof.IselTerms

/-!
# Rule-level evaluation lemmas (interpreter level)

For each probe rule: its match phase on a symbolic CLIF instruction/DFG context (`match_*`),
and its right-hand side from the environment the match builds (`rhs_*`): the value `lower`
returns, the emitted `MInst`s (over vregs) and the fired rules.
-/

namespace Backend.Proof

open Isle Isle.Interp Isle.Aarch64

/-- A three-variable rule environment as the matcher builds it. -/
abbrev env3 (a b c : V) : Interp.Env V :=
  (((Array.replicate 3 none).setIfInBounds 0 (some a)).setIfInBounds 1 (some b)).setIfInBounds 2 (some c)

set_option maxRecDepth 4000 in
theorem instData_iadd (f : Clif.Function) (ty : Clif.Ty) (hty : ty ≠ .i128) (x y : Nat) :
    instData f (.binary .iadd ty x y) = .ok (.data 152 2 [.data 151 73 [], .values [x, y]]) := by
  cases ty <;> first | rfl | exact absurd rfl hty

variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)

include hp in
theorem match_86 {i x y w : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hty : info.resTys.head? = some (.int w)) (hw : w ≤ 64)
    (hd : info.data = .data 152 2 [.data 151 73 [], .values [x, y]]) (st : LState) (tr : Array RuleId) (n : Nat) :
    (matchRule p (sem ctx) cfg (n+2) rule_lower_86 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.value x) (.value y)), (st, tr)) := by
  have h1 := ext_inst_data_value ctx st hi
  rw [hd, hty, Option.getD_some] at h1
  cases hp
  isel_eval [*, rule_lower_86, ext_ty_int_ref_scalar_64_extract ctx st hw, ext_value_array_2]

include hp hc in
theorem rhs_86_32 {x y w : Nat} {rx ry : Reg} (hx : ctx.valueReg? x = some rx)
    (hy : ctx.valueReg? y = some ry) (hw : w ≤ 32) (st : LState) (tr : Array RuleId) (n : Nat) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_86.rhs (env3 (.ty (.int w)) (.value x) (.value y))).run
      (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRR .add .size32 (st.fresh .int).1 rx ry),
          ((((tr.push rule_inst_1592.id).push rule_inst_2545.id).push rule_inst_3118.id).push
            rule_prelude_lower_105.id))) := by
  have h1 := fun st tr n => add_run hp ctx hc st tr n (fun st tr n => operand_size_32 hp ctx hc st tr n hw)
    (emit_add_32 ctx)
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  cases hp
  isel_eval [*, rule_lower_86, ctor_put_in_reg ctx _ hx, ctor_put_in_reg ctx _ hy]

include hp hc in
theorem rhs_86_64 {x y w : Nat} {rx ry : Reg} (hx : ctx.valueReg? x = some rx)
    (hy : ctx.valueReg? y = some ry) (hw : 32 < w) (hw' : w ≤ 64) (st : LState) (tr : Array RuleId) (n : Nat) :
    (evalExpr p (sem ctx) cfg (n+40) rule_lower_86.rhs (env3 (.ty (.int w)) (.value x) (.value y))).run
      (st, tr) =
      .ok (some (.regsVec [[(st.fresh .int).1]]),
        ((st.fresh .int).2.emit (.aluRRR .add .size64 (st.fresh .int).1 rx ry),
          ((((tr.push rule_inst_1593.id).push rule_inst_2545.id).push rule_inst_3118.id).push
            rule_prelude_lower_105.id))) := by
  have h1 := fun st tr n => add_run hp ctx hc st tr n (fun st tr n => operand_size_64 hp ctx hc st tr n hw hw')
    (emit_add_64 ctx)
  have h2 := fun st tr n => output_reg_run hp ctx hc st tr n
  cases hp
  isel_eval [*, rule_lower_86, ctor_put_in_reg ctx _ hx, ctor_put_in_reg ctx _ hy]

end Backend.Proof
