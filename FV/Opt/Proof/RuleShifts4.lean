import FV.Opt.Proof.RuleRestEmbed

/-!
# `opts/shifts.isle` (part 4): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleExtEmbed.lean`, `RuleRestEmbed.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt


set_option maxHeartbeats 16000000 in
/-- `shifts.isle:270`. -/
theorem ok_rule_shifts_270 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_270 := by
  first | rule_auto_xr rule_shifts_270 | rule_auto_xz rule_shifts_270 | rule_auto_v rule_shifts_270

set_option maxHeartbeats 8000000 in
/-- `shifts.isle:280`. -/
theorem ok_rule_shifts_280 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_280 := by
  first | rule_auto_v rule_shifts_280 | rule_auto_w rule_shifts_280

set_option maxHeartbeats 8000000 in
/-- `shifts.isle:285`. -/
theorem ok_rule_shifts_285 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_285 := by
  first | rule_auto_v rule_shifts_285 | rule_auto_w rule_shifts_285

end Opt.Proof
