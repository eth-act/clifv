import FV.Opt.Proof.RuleBitopsEmbed

/-!
# `opts/bitops.isle` (part 7): proven `simplify` rules that need the bitops template variants

`rule_auto_z` (`FV/Opt/Proof/RuleBitopsEmbed.lean`): right-hand sides built by the internal
constructors `all_zero`, `iconst_s ty -1` and `cmp_true`, whose rules take a different arm at
`i128` (`uextend.i128`/`sextend.i128` of an `i64` constant): the type is split on `i128` first.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `bitops.isle:30`. -/
theorem ok_rule_bitops_30 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_30 := by
  rule_auto_z rule_bitops_30

/-- `bitops.isle:49`. -/
theorem ok_rule_bitops_49 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_49 := by
  rule_auto_z rule_bitops_49

/-- `bitops.isle:50`. -/
theorem ok_rule_bitops_50 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_50 := by
  rule_auto_z rule_bitops_50

/-- `bitops.isle:737`. -/
theorem ok_rule_bitops_737 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_737 := by
  rule_auto_z rule_bitops_737

/-- `bitops.isle:738`. -/
theorem ok_rule_bitops_738 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_738 := by
  rule_auto_z rule_bitops_738

/-- `bitops.isle:739`. -/
theorem ok_rule_bitops_739 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_739 := by
  rule_auto_z rule_bitops_739

/-- `bitops.isle:740`. -/
theorem ok_rule_bitops_740 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_740 := by
  rule_auto_z rule_bitops_740

/-- `bitops.isle:743`. -/
theorem ok_rule_bitops_743 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_743 := by
  rule_auto_z rule_bitops_743

/-- `bitops.isle:745`. -/
theorem ok_rule_bitops_745 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_745 := by
  rule_auto_z rule_bitops_745

/-- `bitops.isle:747`. -/
theorem ok_rule_bitops_747 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_747 := by
  rule_auto_z rule_bitops_747

/-- `bitops.isle:749`. -/
theorem ok_rule_bitops_749 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_749 := by
  rule_auto_z rule_bitops_749

/-- `bitops.isle:753`. -/
theorem ok_rule_bitops_753 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_753 := by
  rule_auto_z rule_bitops_753

/-- `bitops.isle:755`. -/
theorem ok_rule_bitops_755 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_755 := by
  rule_auto_z rule_bitops_755

/-- `bitops.isle:757`. -/
theorem ok_rule_bitops_757 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_757 := by
  rule_auto_z rule_bitops_757

/-- `bitops.isle:759`. -/
theorem ok_rule_bitops_759 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_759 := by
  rule_auto_z rule_bitops_759

/-- `bitops.isle:763`. -/
theorem ok_rule_bitops_763 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_763 := by
  rule_auto_z rule_bitops_763

/-- `bitops.isle:764`. -/
theorem ok_rule_bitops_764 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_764 := by
  rule_auto_z rule_bitops_764

/-- `bitops.isle:765`. -/
theorem ok_rule_bitops_765 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_765 := by
  rule_auto_z rule_bitops_765

/-- `bitops.isle:766`. -/
theorem ok_rule_bitops_766 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_766 := by
  rule_auto_z rule_bitops_766

/-- `bitops.isle:767`. -/
theorem ok_rule_bitops_767 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_767 := by
  rule_auto_z rule_bitops_767

/-- `bitops.isle:768`. -/
theorem ok_rule_bitops_768 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_768 := by
  rule_auto_z rule_bitops_768

/-- `bitops.isle:769`. -/
theorem ok_rule_bitops_769 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_769 := by
  rule_auto_z rule_bitops_769

/-- `bitops.isle:770`. -/
theorem ok_rule_bitops_770 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_770 := by
  rule_auto_z rule_bitops_770

/-- `bitops.isle:773`. -/
theorem ok_rule_bitops_773 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_773 := by
  rule_auto_z rule_bitops_773

/-- `bitops.isle:774`. -/
theorem ok_rule_bitops_774 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_774 := by
  rule_auto_z rule_bitops_774

/-- `bitops.isle:775`. -/
theorem ok_rule_bitops_775 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_775 := by
  rule_auto_z rule_bitops_775

/-- `bitops.isle:776`. -/
theorem ok_rule_bitops_776 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_776 := by
  rule_auto_z rule_bitops_776

/-- `bitops.isle:777`. -/
theorem ok_rule_bitops_777 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_777 := by
  rule_auto_z rule_bitops_777

/-- `bitops.isle:778`. -/
theorem ok_rule_bitops_778 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_778 := by
  rule_auto_z rule_bitops_778

/-- `bitops.isle:779`. -/
theorem ok_rule_bitops_779 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_779 := by
  rule_auto_z rule_bitops_779

/-- `bitops.isle:780`. -/
theorem ok_rule_bitops_780 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_780 := by
  rule_auto_z rule_bitops_780

end Opt.Proof
