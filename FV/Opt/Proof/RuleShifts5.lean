import FV.Opt.Proof.RuleRestEmbedSshr
import FV.Opt.Proof.RuleRestEmbedRotl
import FV.Opt.Proof.RuleRestEmbedRotr
import FV.Opt.Proof.RuleIntRetry
import FV.Opt.Proof.RuleInfraShiftAmt

/-!
# `opts/shifts.isle` (part 5): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleExtEmbed.lean`, `RuleRestEmbed.lean`); a `first` chain lists the templates the rule was
checked against, in order. `shifts.isle:152` is `rule_auto_v` whose right-hand side splits the
amount type `kty` of `iconst_u kty` on `isInt` on demand (`RuleIntRetry.lean`): at a float type
the constant has no rule.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

-- In this module `kbv` first tries `kbv_amt` (`RuleInfraShiftAmt.lean`) on the isolated goal, under
-- `kbv_guard` (a failure, also a runtime exception, falls through to the general search).
open Lean Elab Tactic in
local elab_rules : tactic
  | `(tactic| kbv) => Opt.Proof.KernelBV.isolate (do evalTactic (← `(tactic| kbv_guard 200000 kbv_amt)))


set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8000 in
set_option hygiene false in
/-- `shifts.isle:152`. -/
theorem ok_rule_shifts_152 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_152 := by
  rule_intro rule_shifts_152
  rule_lhs hG
  all_goals (try opt_val_ty_subst)
  opt_cases_val
  all_goals opt_split_i128
  all_goals (first | rule_no_iflets | rule_iflets_c [tyMask_ofClif, tyMask_ofClif_i128,
    Rust.tyUmax, panics_throw_bind, except_throw_bind, toExt_throw, Isle.Interp.bindAll,
    Isle.Interp.matchAllN.eq_1, Isle.Interp.matchAllN.eq_2, Isle.Interp.matchArgsN.eq_1,
    imm64Masked_i128, tyInt_ofClif_notInt])
  all_goals opt_int_retry rule_rhs_x [tyMask_ofClif, tyMask_ofClif_i128, Rust.tyUmax,
    panics_throw_bind, except_throw_bind, toExt_throw, Isle.Interp.bindAll,
    Isle.Interp.matchAllN.eq_1, Isle.Interp.matchAllN.eq_2, Isle.Interp.matchArgsN.eq_1,
    imm64Masked_i128, tyInt_ofClif_notInt]
  all_goals (opt_some_subst; (try opt_heq_ite); rule_finish_w)

end Opt.Proof
