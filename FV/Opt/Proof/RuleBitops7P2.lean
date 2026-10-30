import FV.Opt.Proof.RuleIntRetry
import FV.Opt.Proof.RuleFloatArms

/-!
# Part 2 of 4 of `RuleBitops7.lean`

`FV/Opt/Proof/RuleBitops7.lean` imports its parts (split to bound the elaboration memory of a
module; theorems distributed round-robin). See that module for the templates used.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `bitops.isle:49`. -/
theorem ok_rule_bitops_49 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_49 := by
  rule_auto_zi rule_bitops_49

/-- `bitops.isle:739`. -/
theorem ok_rule_bitops_739 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_739 := by
  rule_auto_zi rule_bitops_739

/-- `bitops.isle:747`. -/
theorem ok_rule_bitops_747 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_747 := by
  rule_auto_zi rule_bitops_747

/-- `bitops.isle:757`. -/
theorem ok_rule_bitops_757 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_757 := by
  rule_auto_zi rule_bitops_757

/-- `bitops.isle:765`. -/
theorem ok_rule_bitops_765 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_765 := by
  rule_auto_z rule_bitops_765

/-- `bitops.isle:769`. -/
theorem ok_rule_bitops_769 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_769 := by
  rule_auto_zi rule_bitops_769

/-- `bitops.isle:775`. -/
theorem ok_rule_bitops_775 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_775 := by
  rule_auto_z rule_bitops_775

/-- `bitops.isle:779`. -/
theorem ok_rule_bitops_779 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_779 := by
  rule_auto_zi rule_bitops_779

end Opt.Proof
