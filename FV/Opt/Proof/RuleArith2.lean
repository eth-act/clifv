import FV.Opt.Proof.RuleRestEmbed

/-!
# `opts/arithmetic.isle` (part 2): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleExtEmbed.lean`, `RuleRestEmbed.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt


set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:53`. -/
theorem ok_rule_arithmetic_53 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_53 := by
  first | rule_auto_xr rule_arithmetic_53 | rule_auto_xz rule_arithmetic_53 | rule_auto_w rule_arithmetic_53

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:65`. -/
theorem ok_rule_arithmetic_65 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_65 := by
  first | rule_auto_xr rule_arithmetic_65 | rule_auto_xz rule_arithmetic_65 | rule_auto_w rule_arithmetic_65

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:69`. -/
theorem ok_rule_arithmetic_69 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_69 := by
  first | rule_auto_xr rule_arithmetic_69 | rule_auto_xz rule_arithmetic_69 | rule_auto_w rule_arithmetic_69

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:73`. -/
theorem ok_rule_arithmetic_73 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_73 := by
  first | rule_auto_xr rule_arithmetic_73 | rule_auto_xz rule_arithmetic_73 | rule_auto_w rule_arithmetic_73

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:75`. -/
theorem ok_rule_arithmetic_75 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_75 := by
  first | rule_auto_xr rule_arithmetic_75 | rule_auto_xz rule_arithmetic_75 | rule_auto_w rule_arithmetic_75

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:173`. -/
theorem ok_rule_arithmetic_173 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_173 := by
  first | rule_auto_xr rule_arithmetic_173 | rule_auto_xz rule_arithmetic_173 | rule_auto_w rule_arithmetic_173

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:226`. -/
theorem ok_rule_arithmetic_226 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_226 := by
  first | rule_auto_xr rule_arithmetic_226 | rule_auto_xz rule_arithmetic_226 | rule_auto_w rule_arithmetic_226

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:236`. -/
theorem ok_rule_arithmetic_236 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_236 := by
  first | rule_auto_xr rule_arithmetic_236 | rule_auto_xz rule_arithmetic_236 | rule_auto_w rule_arithmetic_236

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:327`. -/
theorem ok_rule_arithmetic_327 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_327 := by
  first | rule_auto_xr rule_arithmetic_327 | rule_auto_xz rule_arithmetic_327 | rule_auto_w rule_arithmetic_327

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:328`. -/
theorem ok_rule_arithmetic_328 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_328 := by
  first | rule_auto_xr rule_arithmetic_328 | rule_auto_xz rule_arithmetic_328 | rule_auto_w rule_arithmetic_328

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:329`. -/
theorem ok_rule_arithmetic_329 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_329 := by
  first | rule_auto_xr rule_arithmetic_329 | rule_auto_xz rule_arithmetic_329 | rule_auto_w rule_arithmetic_329

end Opt.Proof
