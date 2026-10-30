import FV.Opt.Proof.RuleIntRetry
import FV.Opt.Proof.RuleFloatArms

/-!
# Part 3 of 4 of `RuleBitops7.lean`

`FV/Opt/Proof/RuleBitops7.lean` imports its parts (split to bound the elaboration memory of a
module; theorems distributed round-robin). See that module for the templates used.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `bitops.isle:50`. -/
theorem ok_rule_bitops_50 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_50 := by
  rule_auto_zi rule_bitops_50

/-- `bitops.isle:740`. -/
theorem ok_rule_bitops_740 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_740 := by
  rule_auto_zi rule_bitops_740

/-- `bitops.isle:749`. -/
theorem ok_rule_bitops_749 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_749 := by
  rule_auto_zi rule_bitops_749

/-- `bitops.isle:759`. -/
theorem ok_rule_bitops_759 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_759 := by
  rule_auto_zi rule_bitops_759

/-- `bitops.isle:766`. -/
theorem ok_rule_bitops_766 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_766 := by
  rule_auto_z rule_bitops_766

/-- `bitops.isle:770`. -/
theorem ok_rule_bitops_770 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_770 := by
  rule_auto_zi rule_bitops_770

/-- `bitops.isle:776`. -/
theorem ok_rule_bitops_776 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_776 := by
  rule_auto_z rule_bitops_776

/-- `bitops.isle:780`. -/
theorem ok_rule_bitops_780 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_780 := by
  rule_auto_zi rule_bitops_780

end Opt.Proof
