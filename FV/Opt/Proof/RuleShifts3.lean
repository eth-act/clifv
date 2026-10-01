import FV.Opt.Proof.RuleRestEmbed

/-!
# `opts/shifts.isle` (part 3): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleExtEmbed.lean`, `RuleRestEmbed.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt


set_option maxHeartbeats 16000000 in
/-- `shifts.isle:41`. -/
theorem ok_rule_shifts_41 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_41 := by
  first | rule_auto_xr rule_shifts_41 | rule_auto_xz rule_shifts_41 | rule_auto_v rule_shifts_41

set_option maxHeartbeats 8000000 in
/-- `shifts.isle:50`. -/
theorem ok_rule_shifts_50 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_50 := by
  first | rule_auto_v rule_shifts_50 | rule_auto_w rule_shifts_50

set_option maxHeartbeats 8000000 in
/-- `shifts.isle:61`. -/
theorem ok_rule_shifts_61 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_61 := by
  first | rule_auto_v rule_shifts_61 | rule_auto_w rule_shifts_61

set_option maxHeartbeats 8000000 in
/-- `shifts.isle:71`. -/
theorem ok_rule_shifts_71 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_71 := by
  first | rule_auto_v rule_shifts_71 | rule_auto_w rule_shifts_71

end Opt.Proof
