import FV.Opt.Proof.RuleRestEmbed

/-!
# `opts/cprop.isle` (part 2): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleExtEmbed.lean`, `RuleRestEmbed.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt


set_option maxHeartbeats 4000000 in
/-- `cprop.isle:79`. -/
theorem ok_rule_cprop_79 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_79 := by
  first | rule_auto_xr rule_cprop_79 | rule_auto_xz rule_cprop_79 | rule_auto_w rule_cprop_79

set_option maxHeartbeats 4000000 in
/-- `cprop.isle:84`. -/
theorem ok_rule_cprop_84 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_84 := by
  first | rule_auto_xr rule_cprop_84 | rule_auto_xz rule_cprop_84 | rule_auto_w rule_cprop_84

set_option maxHeartbeats 4000000 in
/-- `cprop.isle:89`. -/
theorem ok_rule_cprop_89 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_89 := by
  first | rule_auto rule_cprop_89 | rule_auto_xr rule_cprop_89

set_option maxHeartbeats 4000000 in
/-- `cprop.isle:94`. -/
theorem ok_rule_cprop_94 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_94 := by
  first | rule_auto rule_cprop_94 | rule_auto_xr rule_cprop_94

set_option maxHeartbeats 4000000 in
/-- `cprop.isle:99`. -/
theorem ok_rule_cprop_99 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_99 := by
  first | rule_auto rule_cprop_99 | rule_auto_xr rule_cprop_99

set_option maxHeartbeats 4000000 in
/-- `cprop.isle:125`. -/
theorem ok_rule_cprop_125 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_125 := by
  rule_auto_v rule_cprop_125

set_option maxHeartbeats 4000000 in
/-- `cprop.isle:130`. -/
theorem ok_rule_cprop_130 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_130 := by
  first | rule_auto_xr rule_cprop_130 | rule_auto_xz rule_cprop_130 | rule_auto_w rule_cprop_130

set_option maxHeartbeats 4000000 in
/-- `cprop.isle:132`. -/
theorem ok_rule_cprop_132 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_132 := by
  rule_auto_v rule_cprop_132

set_option maxHeartbeats 4000000 in
/-- `cprop.isle:135`. -/
theorem ok_rule_cprop_135 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_135 := by
  first | rule_auto_xr rule_cprop_135 | rule_auto_xz rule_cprop_135 | rule_auto_w rule_cprop_135

end Opt.Proof
