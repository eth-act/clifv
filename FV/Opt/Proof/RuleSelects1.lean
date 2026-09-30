import FV.Opt.Proof.RuleIcmpEmbed2

/-!
# `opts/selects.isle` (part 1): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleIcmpEmbed.lean`, `RuleIcmpEmbed2.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `selects.isle:4`. -/
theorem ok_rule_selects_4 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_4 := by
  first | rule_auto rule_selects_4 | rule_auto_b rule_selects_4 | rule_auto_i rule_selects_4 | rule_auto_z rule_selects_4

/-- `selects.isle:9`. -/
theorem ok_rule_selects_9 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_9 := by
  first | rule_auto_c rule_selects_9 | rule_auto_ci rule_selects_9

/-- `selects.isle:20`. -/
theorem ok_rule_selects_20 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_20 := by
  rule_auto_f rule_selects_20

/-- `selects.isle:26`. -/
theorem ok_rule_selects_26 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_26 := by
  first | rule_auto rule_selects_26 | rule_auto_b rule_selects_26 | rule_auto_i rule_selects_26 | rule_auto_z rule_selects_26

/-- `selects.isle:27`. -/
theorem ok_rule_selects_27 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_27 := by
  first | rule_auto rule_selects_27 | rule_auto_b rule_selects_27 | rule_auto_i rule_selects_27 | rule_auto_z rule_selects_27

/-- `selects.isle:28`. -/
theorem ok_rule_selects_28 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_28 := by
  first | rule_auto rule_selects_28 | rule_auto_b rule_selects_28 | rule_auto_i rule_selects_28 | rule_auto_z rule_selects_28

/-- `selects.isle:29`. -/
theorem ok_rule_selects_29 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_29 := by
  first | rule_auto rule_selects_29 | rule_auto_b rule_selects_29 | rule_auto_i rule_selects_29 | rule_auto_z rule_selects_29

/-- `selects.isle:30`. -/
theorem ok_rule_selects_30 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_30 := by
  first | rule_auto rule_selects_30 | rule_auto_b rule_selects_30 | rule_auto_i rule_selects_30 | rule_auto_z rule_selects_30

/-- `selects.isle:31`. -/
theorem ok_rule_selects_31 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_31 := by
  first | rule_auto rule_selects_31 | rule_auto_b rule_selects_31 | rule_auto_i rule_selects_31 | rule_auto_z rule_selects_31

/-- `selects.isle:32`. -/
theorem ok_rule_selects_32 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_32 := by
  first | rule_auto rule_selects_32 | rule_auto_b rule_selects_32 | rule_auto_i rule_selects_32 | rule_auto_z rule_selects_32

/-- `selects.isle:33`. -/
theorem ok_rule_selects_33 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_33 := by
  first | rule_auto rule_selects_33 | rule_auto_b rule_selects_33 | rule_auto_i rule_selects_33 | rule_auto_z rule_selects_33

/-- `selects.isle:36`. -/
theorem ok_rule_selects_36 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_36 := by
  first | rule_auto rule_selects_36 | rule_auto_b rule_selects_36 | rule_auto_i rule_selects_36 | rule_auto_z rule_selects_36

/-- `selects.isle:37`. -/
theorem ok_rule_selects_37 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_37 := by
  first | rule_auto rule_selects_37 | rule_auto_b rule_selects_37 | rule_auto_i rule_selects_37 | rule_auto_z rule_selects_37

end Opt.Proof
