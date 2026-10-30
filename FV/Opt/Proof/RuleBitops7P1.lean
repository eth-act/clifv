import FV.Opt.Proof.RuleIntRetry
import FV.Opt.Proof.RuleFloatArms

/-!
# Part 1 of 4 of `RuleBitops7.lean`

`FV/Opt/Proof/RuleBitops7.lean` imports its parts (split to bound the elaboration memory of a
module; theorems distributed round-robin). See that module for the templates used.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `bitops.isle:30`. -/
theorem ok_rule_bitops_30 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_30 := by
  rule_auto_zi rule_bitops_30

/-- `bitops.isle:738`. -/
theorem ok_rule_bitops_738 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_738 := by
  rule_auto_zi rule_bitops_738

/-- `bitops.isle:745`. -/
theorem ok_rule_bitops_745 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_745 := by
  rule_auto_zi rule_bitops_745

/-- `bitops.isle:755`. -/
theorem ok_rule_bitops_755 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_755 := by
  rule_auto_zi rule_bitops_755

/-- `bitops.isle:764`. -/
theorem ok_rule_bitops_764 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_764 := by
  rule_auto_z rule_bitops_764

/-- `bitops.isle:768`. -/
theorem ok_rule_bitops_768 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_768 := by
  rule_auto_zi rule_bitops_768

/-- `bitops.isle:774`. -/
theorem ok_rule_bitops_774 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_774 := by
  rule_auto_z rule_bitops_774

/-- `bitops.isle:778`. -/
theorem ok_rule_bitops_778 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_778 := by
  rule_auto_zi rule_bitops_778

end Opt.Proof
