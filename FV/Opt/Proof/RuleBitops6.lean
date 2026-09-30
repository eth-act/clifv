import FV.Opt.Proof.RuleBitopsEmbed

/-!
# `opts/bitops.isle` (part 6): proven `simplify` rules that need the bitops template variants

`rule_auto_b` (`FV/Opt/Proof/RuleBitopsEmbed.lean`): the `all_zero`/`iconst_s` extractors on the
left-hand side, `bswap`/`bitrev`/`popcnt` identities, `bmask` of an untyped operand value, and a
type variable bound twice. `rule_auto_i`: rules with Boolean if-lets (`sshr ... (iconst_u
shift)` with `shift = ty_shift_mask ty`).
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `bitops.isle:21`. -/
theorem ok_rule_bitops_21 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_21 := by
  rule_auto_b rule_bitops_21

/-- `bitops.isle:22`. -/
theorem ok_rule_bitops_22 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_22 := by
  rule_auto_b rule_bitops_22

/-- `bitops.isle:26`. -/
theorem ok_rule_bitops_26 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_26 := by
  rule_auto_b rule_bitops_26

/-- `bitops.isle:27`. -/
theorem ok_rule_bitops_27 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_27 := by
  rule_auto_b rule_bitops_27

/-- `bitops.isle:41`. -/
theorem ok_rule_bitops_41 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_41 := by
  rule_auto_b rule_bitops_41

/-- `bitops.isle:45`. -/
theorem ok_rule_bitops_45 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_45 := by
  rule_auto_b rule_bitops_45

/-- `bitops.isle:46`. -/
theorem ok_rule_bitops_46 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_46 := by
  rule_auto_b rule_bitops_46

/-- `bitops.isle:87`. -/
theorem ok_rule_bitops_87 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_87 := by
  rule_auto_b rule_bitops_87

/-- `bitops.isle:94`. -/
theorem ok_rule_bitops_94 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_94 := by
  rule_auto_i rule_bitops_94

/-- `bitops.isle:98`. -/
theorem ok_rule_bitops_98 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_98 := by
  rule_auto_i rule_bitops_98

/-- `bitops.isle:139`. -/
theorem ok_rule_bitops_139 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_139 := by
  rule_auto_b rule_bitops_139

/-- `bitops.isle:140`. -/
theorem ok_rule_bitops_140 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_140 := by
  rule_auto_b rule_bitops_140

/-- `bitops.isle:143`. -/
theorem ok_rule_bitops_143 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_143 := by
  rule_auto_b rule_bitops_143

/-- `bitops.isle:146`. -/
theorem ok_rule_bitops_146 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_146 := by
  rule_auto_b rule_bitops_146

/-- `bitops.isle:400`. -/
theorem ok_rule_bitops_400 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_400 := by
  rule_auto_b rule_bitops_400

/-- `bitops.isle:405`. -/
theorem ok_rule_bitops_405 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_405 := by
  rule_auto_b rule_bitops_405

/-- `bitops.isle:410`. -/
theorem ok_rule_bitops_410 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_410 := by
  rule_auto_b rule_bitops_410

/-- `bitops.isle:415`. -/
theorem ok_rule_bitops_415 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_415 := by
  rule_auto_b rule_bitops_415

/-- `bitops.isle:789`. -/
theorem ok_rule_bitops_789 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_789 := by
  rule_auto_b rule_bitops_789

/-- `bitops.isle:792`. -/
theorem ok_rule_bitops_792 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_792 := by
  rule_auto_b rule_bitops_792

end Opt.Proof
