import FV.Opt.Proof.RuleRestEmbedBase

/-!
# Splitting type variables on `isInt`

A constructor such as `iconst_s ty c` or `iconst_u ty c` on the right of a rule matches
`ty_int ty`, and `Rust.tyInt (CTy.ofClif ty)` only evaluates once `ty` is known to be an
integer (`tyInt_ofClif`) or not (`tyInt_ofClif_notInt`); `opt_eval` discharges either side
condition by `assumption`. `opt_split_int` provides that hypothesis for every type variable.
At a float type the right-hand constructor has no matching rule and the evaluation throws.
After `opt_cases_ty` the type is concrete; `tyInt_ofClif_f32`/`tyInt_ofClif_f64` evaluate
the float arms there.
-/

namespace Opt.Proof

open Isle Isle.Opt Clif

theorem tyInt_ofClif_notInt {t : Ty} (h : ¬t.isInt = true) :
    Rust.tyInt (CTy.ofClif t) = none := by
  cases t <;> first | rfl | exact absurd rfl h

theorem tyInt_ofClif_f32 : Rust.tyInt (CTy.ofClif .f32) = none := rfl
theorem tyInt_ofClif_f64 : Rust.tyInt (CTy.ofClif .f64) = none := rfl

open Lean Meta Elab Tactic in
/-- `opt_split_int_one`: for the first local `t : Clif.Ty` without a hypothesis
`t.isInt = true` or `¬t.isInt = true`, split on `t.isInt = true`; fails if there is none. -/
elab "opt_split_int_one" : tactic => withMainContext do
  let lctx ← getLCtx
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isConstOf ``Clif.Ty do continue
    let x := d.toExpr
    let mut has := false
    for d' in lctx do
      if d'.isImplementationDetail then continue
      let t ← instantiateMVars d'.type
      let t := if t.isAppOfArity ``Not 1 then t.appArg! else t
      if t.isAppOfArity ``Eq 3 && t.appFn!.appArg!.isAppOfArity ``Clif.Ty.isInt 1 &&
          t.appFn!.appArg!.appArg! == x then
        has := true
        break
    if has then continue
    let xs ← Term.exprToSyntax x
    evalTactic (← `(tactic| rcases Classical.em (Clif.Ty.isInt $xs = true) with hint | hint))
    return
  throwError "opt_split_int_one: nothing to split"

/-- Split every `Clif.Ty` local on `isInt`. -/
macro "opt_split_int" : tactic => `(tactic| repeat (any_goals opt_split_int_one))

/-- `rule_auto_xz` with the type variables split on `isInt` before the if-lets. -/
syntax "rule_auto_xzi " ident : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_xzi $r:ident) => `(tactic| (
      rule_intro $r
      rule_lhs hG
      all_goals (try opt_val_ty_subst)
      opt_cases_val
      all_goals opt_split_i128
      all_goals opt_split_int
      all_goals (first | rule_no_iflets | rule_iflets_c [tyMask_ofClif, tyMask_ofClif_i128,
        Rust.tyUmax, panics_throw_bind, except_throw_bind, toExt_throw, tyInt_ofClif_notInt])
      all_goals (
        rule_rhs_x [tyMask_ofClif, tyMask_ofClif_i128, Rust.tyUmax, panics_throw_bind,
          except_throw_bind, toExt_throw, tyInt_ofClif_notInt]
        all_goals (opt_some_subst; rule_finish_x))))

/-- `rule_auto_v` with the type variables split on `isInt` before the if-lets. -/
syntax "rule_auto_vi " ident : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_vi $r:ident) => `(tactic| (
      rule_intro $r
      rule_lhs hG
      all_goals (try opt_val_ty_subst)
      opt_cases_val
      all_goals opt_split_i128
      all_goals opt_split_int
      all_goals (first | rule_no_iflets | rule_iflets_c [tyMask_ofClif, tyMask_ofClif_i128,
        Rust.tyUmax, panics_throw_bind, except_throw_bind, toExt_throw, Isle.Interp.bindAll,
        Isle.Interp.matchAllN.eq_1, Isle.Interp.matchAllN.eq_2, Isle.Interp.matchArgsN.eq_1,
        imm64Masked_i128, tyInt_ofClif_notInt])
      all_goals (
        rule_rhs_x [tyMask_ofClif, tyMask_ofClif_i128, Rust.tyUmax, panics_throw_bind,
          except_throw_bind, toExt_throw, Isle.Interp.bindAll, Isle.Interp.matchAllN.eq_1,
          Isle.Interp.matchAllN.eq_2, Isle.Interp.matchArgsN.eq_1, imm64Masked_i128,
          tyInt_ofClif_notInt]
        all_goals (opt_some_subst; (try opt_heq_ite); rule_finish_w))))

example : Rust.tyInt (CTy.ofClif .f32) = none := tyInt_ofClif_notInt (by decide)

end Opt.Proof
