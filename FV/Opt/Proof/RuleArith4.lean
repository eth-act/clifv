import FV.Opt.Proof.RuleRestEmbed

/-!
# `opts/arithmetic.isle` (part 4): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleExtEmbed.lean`, `RuleRestEmbed.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt


set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:437`. -/
theorem ok_rule_arithmetic_437 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_437 := by
  first | rule_auto_xr rule_arithmetic_437 | rule_auto_v rule_arithmetic_437 | rule_auto_w rule_arithmetic_437

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:438`. -/
theorem ok_rule_arithmetic_438 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_438 := by
  first | rule_auto_xr rule_arithmetic_438 | rule_auto_v rule_arithmetic_438 | rule_auto_w rule_arithmetic_438

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:441`. -/
theorem ok_rule_arithmetic_441 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_441 := by
  first | rule_auto_xr rule_arithmetic_441 | rule_auto_v rule_arithmetic_441 | rule_auto_w rule_arithmetic_441

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:442`. -/
theorem ok_rule_arithmetic_442 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_442 := by
  first | rule_auto_xr rule_arithmetic_442 | rule_auto_v rule_arithmetic_442 | rule_auto_w rule_arithmetic_442

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:443`. -/
theorem ok_rule_arithmetic_443 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_443 := by
  first | rule_auto_xr rule_arithmetic_443 | rule_auto_v rule_arithmetic_443 | rule_auto_w rule_arithmetic_443

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:444`. -/
theorem ok_rule_arithmetic_444 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_444 := by
  first | rule_auto_xr rule_arithmetic_444 | rule_auto_v rule_arithmetic_444 | rule_auto_w rule_arithmetic_444

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:445`. -/
theorem ok_rule_arithmetic_445 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_445 := by
  first | rule_auto_xr rule_arithmetic_445 | rule_auto_v rule_arithmetic_445 | rule_auto_w rule_arithmetic_445

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:446`. -/
theorem ok_rule_arithmetic_446 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_446 := by
  first | rule_auto_xr rule_arithmetic_446 | rule_auto_v rule_arithmetic_446 | rule_auto_w rule_arithmetic_446

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:447`. -/
theorem ok_rule_arithmetic_447 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_447 := by
  first | rule_auto_xr rule_arithmetic_447 | rule_auto_v rule_arithmetic_447 | rule_auto_w rule_arithmetic_447

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:448`. -/
theorem ok_rule_arithmetic_448 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_448 := by
  first | rule_auto_xr rule_arithmetic_448 | rule_auto_v rule_arithmetic_448 | rule_auto_w rule_arithmetic_448

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:577`. -/
theorem ok_rule_arithmetic_577 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_577 := by
  first | rule_auto_xr rule_arithmetic_577 | rule_auto_v rule_arithmetic_577 | rule_auto_w rule_arithmetic_577

end Opt.Proof
