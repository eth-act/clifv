import FV.Opt.Proof.RuleIcmpEmbed2

/-!
# `opts/icmp.isle` (part 4): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleIcmpEmbed.lean`, `RuleIcmpEmbed2.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `icmp.isle:299`. -/
theorem ok_rule_icmp_299 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_299 := by
  first | rule_auto rule_icmp_299 | rule_auto_b rule_icmp_299 | rule_auto_i rule_icmp_299 | rule_auto_z rule_icmp_299

/-- `icmp.isle:300`. -/
theorem ok_rule_icmp_300 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_300 := by
  first | rule_auto rule_icmp_300 | rule_auto_b rule_icmp_300 | rule_auto_i rule_icmp_300 | rule_auto_z rule_icmp_300

/-- `icmp.isle:303`. -/
theorem ok_rule_icmp_303 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_303 := by
  first | rule_auto rule_icmp_303 | rule_auto_b rule_icmp_303 | rule_auto_i rule_icmp_303 | rule_auto_z rule_icmp_303

/-- `icmp.isle:304`. -/
theorem ok_rule_icmp_304 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_304 := by
  first | rule_auto rule_icmp_304 | rule_auto_b rule_icmp_304 | rule_auto_i rule_icmp_304 | rule_auto_z rule_icmp_304

/-- `icmp.isle:306`. -/
theorem ok_rule_icmp_306 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_306 := by
  first | rule_auto rule_icmp_306 | rule_auto_b rule_icmp_306 | rule_auto_i rule_icmp_306 | rule_auto_z rule_icmp_306

/-- `icmp.isle:307`. -/
theorem ok_rule_icmp_307 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_307 := by
  first | rule_auto rule_icmp_307 | rule_auto_b rule_icmp_307 | rule_auto_i rule_icmp_307 | rule_auto_z rule_icmp_307

end Opt.Proof
