import FV.Opt.Proof.RuleSkelEmbed
import FV.Opt.Proof.RuleIntSplit

/-!
# Proven `simplify_skeleton` rules

`ok_rule_X : SkelRuleOk p rule_X` for the skeleton rules in `Opt.provenSkeletonRules`
(`FV/Opt/RuleAllow.lean`), with the templates of `FV/Opt/Proof/RuleSkelEmbed.lean`:
`skel_auto_div` (a division by a constant replaced by a value), `skel_auto_br` (conditional
traps and branches with a known condition, branches to trap blocks) and `skel_auto_truthy` (a
condition stripped by `truthy`).
-/

namespace Opt.Proof

open Isle Isle.Opt Isle.Interp Clif

attribute [local opt_monad] tyInt_ofClif_notInt panics_throw_bind except_throw_bind toExt_throw
  except_throw_bind'

set_option hygiene false in
/-- `skel_auto_div` with the type variables split on `isInt` (`RuleIntSplit.lean`): at a float
type the made `iconst_u` has no rule (`tyInt_ofClif_notInt`) and the evaluation throws. -/
local macro "skel_auto_div_int " r:ident : tactic => `(tactic| (
  skel_intro $r
  rule_no_iflets
  rule_lhs hG
  skel_reads
  rule_lhs hG
  all_goals opt_split_int
  all_goals first
    | skel_rhs
    | (opt_eval hev
       repeat' (split at hev <;> try opt_norm hev)
       all_goals (simp only [reduceCtorEq] at hev))
  all_goals (skel_good; skel_div)))

set_option maxHeartbeats 4000000 in
theorem ok_rule_arithmetic_79 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_arithmetic_79 := by
  skel_auto_div rule_arithmetic_79

set_option maxHeartbeats 4000000 in
theorem ok_rule_arithmetic_80 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_arithmetic_80 := by
  skel_auto_div rule_arithmetic_80

set_option maxHeartbeats 4000000 in
theorem ok_rule_arithmetic_130 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_arithmetic_130 := by
  skel_auto_div_int rule_arithmetic_130

set_option maxHeartbeats 4000000 in
theorem ok_rule_arithmetic_131 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_arithmetic_131 := by
  skel_auto_div_int rule_arithmetic_131

set_option maxHeartbeats 4000000 in
theorem ok_rule_arithmetic_132 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_arithmetic_132 := by
  skel_auto_div_int rule_arithmetic_132

set_option maxHeartbeats 4000000 in
theorem ok_rule_cprop_32 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_cprop_32 := by
  skel_auto_div_i rule_cprop_32

set_option maxHeartbeats 4000000 in
theorem ok_rule_cprop_38 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_cprop_38 := by
  skel_auto_div_i rule_cprop_38

set_option maxHeartbeats 4000000 in
theorem ok_rule_cprop_44 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_cprop_44 := by
  skel_auto_div_i rule_cprop_44

set_option maxHeartbeats 4000000 in
theorem ok_rule_cprop_50 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_cprop_50 := by
  skel_auto_div_i rule_cprop_50

set_option maxHeartbeats 4000000 in
theorem ok_rule_skeleton_7 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_skeleton_7 := by
  skel_auto_br rule_skeleton_7

set_option maxHeartbeats 4000000 in
theorem ok_rule_skeleton_9 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_skeleton_9 := by
  skel_auto_br rule_skeleton_9

set_option maxHeartbeats 4000000 in
theorem ok_rule_skeleton_22 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_skeleton_22 := by
  skel_auto_br rule_skeleton_22

set_option maxHeartbeats 4000000 in
theorem ok_rule_skeleton_26 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_skeleton_26 := by
  skel_auto_br rule_skeleton_26

set_option maxHeartbeats 4000000 in
theorem ok_rule_skeleton_33 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_skeleton_33 := by
  skel_auto_br rule_skeleton_33

set_option maxHeartbeats 4000000 in
theorem ok_rule_skeleton_37 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_skeleton_37 := by
  skel_auto_br rule_skeleton_37

set_option maxHeartbeats 4000000 in
theorem ok_rule_skeleton_44 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_skeleton_44 := by
  skel_auto_br rule_skeleton_44

set_option maxHeartbeats 4000000 in
theorem ok_rule_skeleton_50 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_skeleton_50 := by
  skel_auto_truthy rule_skeleton_50

set_option maxHeartbeats 4000000 in
theorem ok_rule_skeleton_53 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_skeleton_53 := by
  skel_auto_truthy rule_skeleton_53

set_option maxHeartbeats 4000000 in
theorem ok_rule_skeleton_56 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_skeleton_56 := by
  skel_auto_truthy rule_skeleton_56

end Opt.Proof
