import FV.Opt.Proof.RuleRestEmbed

/-!
# `opts/icmp.isle` (part 9): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleExtEmbed.lean`, `RuleRestEmbed.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt


set_option maxHeartbeats 4000000 in
/-- `icmp.isle:196`. -/
theorem ok_rule_icmp_196 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_196 := by
  rule_auto_v rule_icmp_196

set_option maxHeartbeats 4000000 in
/-- `icmp.isle:199`. -/
theorem ok_rule_icmp_199 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_199 := by
  rule_auto_v rule_icmp_199

set_option maxHeartbeats 4000000 in
/-- `icmp.isle:202`. -/
theorem ok_rule_icmp_202 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_202 := by
  rule_auto_v rule_icmp_202

end Opt.Proof
