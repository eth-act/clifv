import FV.Opt.Proof.RuleRestEmbed

/-!
# `opts/arithmetic.isle` (part 3): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleExtEmbed.lean`, `RuleRestEmbed.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt


set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:330`. -/
theorem ok_rule_arithmetic_330 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_330 := by
  first | rule_auto_xr rule_arithmetic_330 | rule_auto_xz rule_arithmetic_330 | rule_auto_w rule_arithmetic_330

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:404`. -/
theorem ok_rule_arithmetic_404 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_404 := by
  first | rule_auto_xr rule_arithmetic_404 | rule_auto_xz rule_arithmetic_404 | rule_auto_w rule_arithmetic_404

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:405`. -/
theorem ok_rule_arithmetic_405 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_405 := by
  first | rule_auto_xr rule_arithmetic_405 | rule_auto_xz rule_arithmetic_405 | rule_auto_w rule_arithmetic_405

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:406`. -/
theorem ok_rule_arithmetic_406 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_406 := by
  first | rule_auto_xr rule_arithmetic_406 | rule_auto_xz rule_arithmetic_406 | rule_auto_w rule_arithmetic_406

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:407`. -/
theorem ok_rule_arithmetic_407 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_407 := by
  first | rule_auto_xr rule_arithmetic_407 | rule_auto_xz rule_arithmetic_407 | rule_auto_w rule_arithmetic_407

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:431`. -/
theorem ok_rule_arithmetic_431 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_431 := by
  first | rule_auto_xr rule_arithmetic_431 | rule_auto_v rule_arithmetic_431 | rule_auto_w rule_arithmetic_431

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:432`. -/
theorem ok_rule_arithmetic_432 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_432 := by
  first | rule_auto_xr rule_arithmetic_432 | rule_auto_v rule_arithmetic_432 | rule_auto_w rule_arithmetic_432

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:433`. -/
theorem ok_rule_arithmetic_433 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_433 := by
  first | rule_auto_xr rule_arithmetic_433 | rule_auto_v rule_arithmetic_433 | rule_auto_w rule_arithmetic_433

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:434`. -/
theorem ok_rule_arithmetic_434 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_434 := by
  first | rule_auto_xr rule_arithmetic_434 | rule_auto_v rule_arithmetic_434 | rule_auto_w rule_arithmetic_434

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:435`. -/
theorem ok_rule_arithmetic_435 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_435 := by
  first | rule_auto_xr rule_arithmetic_435 | rule_auto_v rule_arithmetic_435 | rule_auto_w rule_arithmetic_435

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:436`. -/
theorem ok_rule_arithmetic_436 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_436 := by
  first | rule_auto_xr rule_arithmetic_436 | rule_auto_v rule_arithmetic_436 | rule_auto_w rule_arithmetic_436

end Opt.Proof
