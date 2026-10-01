import FV.Opt.Proof.RuleRestEmbed

/-!
# `opts/arithmetic.isle` (part 5): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleExtEmbed.lean`, `RuleRestEmbed.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt


set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:578`. -/
theorem ok_rule_arithmetic_578 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_578 := by
  first | rule_auto_xr rule_arithmetic_578 | rule_auto_v rule_arithmetic_578 | rule_auto_w rule_arithmetic_578

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:579`. -/
theorem ok_rule_arithmetic_579 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_579 := by
  first | rule_auto_xr rule_arithmetic_579 | rule_auto_v rule_arithmetic_579 | rule_auto_w rule_arithmetic_579

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:580`. -/
theorem ok_rule_arithmetic_580 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_580 := by
  first | rule_auto_xr rule_arithmetic_580 | rule_auto_v rule_arithmetic_580 | rule_auto_w rule_arithmetic_580

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:581`. -/
theorem ok_rule_arithmetic_581 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_581 := by
  first | rule_auto_xr rule_arithmetic_581 | rule_auto_v rule_arithmetic_581 | rule_auto_w rule_arithmetic_581

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:582`. -/
theorem ok_rule_arithmetic_582 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_582 := by
  first | rule_auto_xr rule_arithmetic_582 | rule_auto_v rule_arithmetic_582 | rule_auto_w rule_arithmetic_582

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:583`. -/
theorem ok_rule_arithmetic_583 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_583 := by
  first | rule_auto_xr rule_arithmetic_583 | rule_auto_v rule_arithmetic_583 | rule_auto_w rule_arithmetic_583

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:584`. -/
theorem ok_rule_arithmetic_584 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_584 := by
  first | rule_auto_xr rule_arithmetic_584 | rule_auto_v rule_arithmetic_584 | rule_auto_w rule_arithmetic_584

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:607`. -/
theorem ok_rule_arithmetic_607 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_607 := by
  first | rule_auto_xr rule_arithmetic_607 | rule_auto_v rule_arithmetic_607 | rule_auto_w rule_arithmetic_607

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:610`. -/
theorem ok_rule_arithmetic_610 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_610 := by
  first | rule_auto_xr rule_arithmetic_610 | rule_auto_v rule_arithmetic_610 | rule_auto_w rule_arithmetic_610

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:611`. -/
theorem ok_rule_arithmetic_611 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_611 := by
  first | rule_auto_xr rule_arithmetic_611 | rule_auto_v rule_arithmetic_611 | rule_auto_w rule_arithmetic_611

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:612`. -/
theorem ok_rule_arithmetic_612 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_612 := by
  first | rule_auto_xr rule_arithmetic_612 | rule_auto_v rule_arithmetic_612 | rule_auto_w rule_arithmetic_612

end Opt.Proof
