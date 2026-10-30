import FV.Opt.Proof.RuleIntRetry
import FV.Opt.Proof.RuleFloatArms

/-!
# Part 4 of 4 of `RuleBitops7.lean`

`FV/Opt/Proof/RuleBitops7.lean` imports its parts (split to bound the elaboration memory of a
module; theorems distributed round-robin). See that module for the templates used.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `bitops.isle:737`. -/
theorem ok_rule_bitops_737 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_737 := by
  rule_auto_zi rule_bitops_737

/-- `bitops.isle:743`. -/
theorem ok_rule_bitops_743 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_743 := by
  rule_auto_zi rule_bitops_743

/-- `bitops.isle:753`. -/
theorem ok_rule_bitops_753 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_753 := by
  rule_auto_zi rule_bitops_753

/-- `bitops.isle:763`. -/
theorem ok_rule_bitops_763 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_763 := by
  rule_auto_z rule_bitops_763

/-- `bitops.isle:767`. -/
theorem ok_rule_bitops_767 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_767 := by
  rule_auto_zi rule_bitops_767

/-- `bitops.isle:773`. -/
theorem ok_rule_bitops_773 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_773 := by
  rule_auto_z rule_bitops_773

/-- `bitops.isle:777`. -/
theorem ok_rule_bitops_777 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_777 := by
  rule_auto_zi rule_bitops_777

end Opt.Proof
