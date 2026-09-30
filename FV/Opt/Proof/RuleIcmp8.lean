import FV.Opt.Proof.RuleIcmpEmbed2

/-!
# `opts/icmp.isle` (part 8): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleIcmpEmbed.lean`, `RuleIcmpEmbed2.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `icmp.isle:513`. -/
theorem ok_rule_icmp_513 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_513 := by
  first | rule_auto rule_icmp_513 | rule_auto_b rule_icmp_513 | rule_auto_i rule_icmp_513 | rule_auto_z rule_icmp_513

/-- `icmp.isle:514`. -/
theorem ok_rule_icmp_514 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_514 := by
  first | rule_auto rule_icmp_514 | rule_auto_b rule_icmp_514 | rule_auto_i rule_icmp_514 | rule_auto_z rule_icmp_514

/-- `icmp.isle:517`. -/
theorem ok_rule_icmp_517 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_517 := by
  first | rule_auto rule_icmp_517 | rule_auto_b rule_icmp_517 | rule_auto_i rule_icmp_517 | rule_auto_z rule_icmp_517

/-- `icmp.isle:520`. -/
theorem ok_rule_icmp_520 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_520 := by
  first | rule_auto rule_icmp_520 | rule_auto_b rule_icmp_520 | rule_auto_i rule_icmp_520 | rule_auto_z rule_icmp_520

/-- `icmp.isle:523`. -/
theorem ok_rule_icmp_523 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_523 := by
  first | rule_auto rule_icmp_523 | rule_auto_b rule_icmp_523 | rule_auto_i rule_icmp_523 | rule_auto_z rule_icmp_523

/-- `icmp.isle:526`. -/
theorem ok_rule_icmp_526 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_526 := by
  first | rule_auto rule_icmp_526 | rule_auto_b rule_icmp_526 | rule_auto_i rule_icmp_526 | rule_auto_z rule_icmp_526

/-- `icmp.isle:529`. -/
theorem ok_rule_icmp_529 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_529 := by
  first | rule_auto rule_icmp_529 | rule_auto_b rule_icmp_529 | rule_auto_i rule_icmp_529 | rule_auto_z rule_icmp_529

/-- `icmp.isle:532`. -/
theorem ok_rule_icmp_532 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_532 := by
  first | rule_auto rule_icmp_532 | rule_auto_b rule_icmp_532 | rule_auto_i rule_icmp_532 | rule_auto_z rule_icmp_532

/-- `icmp.isle:535`. -/
theorem ok_rule_icmp_535 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_535 := by
  first | rule_auto rule_icmp_535 | rule_auto_b rule_icmp_535 | rule_auto_i rule_icmp_535 | rule_auto_z rule_icmp_535

end Opt.Proof
