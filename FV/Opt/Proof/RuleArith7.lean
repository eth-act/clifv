import FV.Opt.Proof.RuleInfraConst

/-!
# `opts/arithmetic.isle` (part 7): constants made at the rule's type variable

`iconst_u ty k` / `iconst_s ty k` / `iconst ty (imm64_neg ty c)` on the right-hand side (and
`isub (isub x y) (isub x z)`), by `rule_auto_tv` (`RuleInfraConst.lean`).
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:50`. -/
theorem ok_rule_arithmetic_50 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_50 := by
  rule_auto_tv rule_arithmetic_50

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:333`. -/
theorem ok_rule_arithmetic_333 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_333 := by
  rule_auto_tv rule_arithmetic_333

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:334`. -/
theorem ok_rule_arithmetic_334 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_334 := by
  rule_auto_tv rule_arithmetic_334

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:343`. -/
theorem ok_rule_arithmetic_343 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_343 := by
  rule_auto_tv rule_arithmetic_343

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:349`. -/
theorem ok_rule_arithmetic_349 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_349 := by
  rule_auto_tv rule_arithmetic_349

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:587`. -/
theorem ok_rule_arithmetic_587 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_587 := by
  rule_auto_tv rule_arithmetic_587

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:590`. -/
theorem ok_rule_arithmetic_590 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_590 := by
  rule_auto_tv rule_arithmetic_590

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:593`. -/
theorem ok_rule_arithmetic_593 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_593 := by
  rule_auto_tv rule_arithmetic_593

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:596`. -/
theorem ok_rule_arithmetic_596 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_596 := by
  rule_auto_tv rule_arithmetic_596

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:603`. -/
theorem ok_rule_arithmetic_603 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_603 := by
  rule_auto_tv rule_arithmetic_603

end Opt.Proof
