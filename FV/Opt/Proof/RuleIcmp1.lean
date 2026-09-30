import FV.Opt.Proof.RuleIcmpEmbed2

/-!
# `opts/icmp.isle` (part 1): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleIcmpEmbed.lean`, `RuleIcmpEmbed2.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `icmp.isle:5`. -/
theorem ok_rule_icmp_5 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_5 := by
  first | rule_auto rule_icmp_5 | rule_auto_b rule_icmp_5 | rule_auto_i rule_icmp_5 | rule_auto_z rule_icmp_5

/-- `icmp.isle:6`. -/
theorem ok_rule_icmp_6 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_6 := by
  first | rule_auto rule_icmp_6 | rule_auto_b rule_icmp_6 | rule_auto_i rule_icmp_6 | rule_auto_z rule_icmp_6

/-- `icmp.isle:7`. -/
theorem ok_rule_icmp_7 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_7 := by
  first | rule_auto rule_icmp_7 | rule_auto_b rule_icmp_7 | rule_auto_i rule_icmp_7 | rule_auto_z rule_icmp_7

/-- `icmp.isle:8`. -/
theorem ok_rule_icmp_8 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_8 := by
  first | rule_auto rule_icmp_8 | rule_auto_b rule_icmp_8 | rule_auto_i rule_icmp_8 | rule_auto_z rule_icmp_8

/-- `icmp.isle:9`. -/
theorem ok_rule_icmp_9 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_9 := by
  first | rule_auto rule_icmp_9 | rule_auto_b rule_icmp_9 | rule_auto_i rule_icmp_9 | rule_auto_z rule_icmp_9

/-- `icmp.isle:10`. -/
theorem ok_rule_icmp_10 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_10 := by
  first | rule_auto rule_icmp_10 | rule_auto_b rule_icmp_10 | rule_auto_i rule_icmp_10 | rule_auto_z rule_icmp_10

/-- `icmp.isle:11`. -/
theorem ok_rule_icmp_11 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_11 := by
  first | rule_auto rule_icmp_11 | rule_auto_b rule_icmp_11 | rule_auto_i rule_icmp_11 | rule_auto_z rule_icmp_11

/-- `icmp.isle:12`. -/
theorem ok_rule_icmp_12 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_12 := by
  first | rule_auto rule_icmp_12 | rule_auto_b rule_icmp_12 | rule_auto_i rule_icmp_12 | rule_auto_z rule_icmp_12

/-- `icmp.isle:13`. -/
theorem ok_rule_icmp_13 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_13 := by
  first | rule_auto rule_icmp_13 | rule_auto_b rule_icmp_13 | rule_auto_i rule_icmp_13 | rule_auto_z rule_icmp_13

/-- `icmp.isle:14`. -/
theorem ok_rule_icmp_14 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_14 := by
  first | rule_auto rule_icmp_14 | rule_auto_b rule_icmp_14 | rule_auto_i rule_icmp_14 | rule_auto_z rule_icmp_14

/-- `icmp.isle:21`. -/
theorem ok_rule_icmp_21 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_21 := by
  first | rule_auto_c rule_icmp_21 | rule_auto_ci rule_icmp_21

/-- `icmp.isle:23`. -/
theorem ok_rule_icmp_23 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_23 := by
  first | rule_auto_c rule_icmp_23 | rule_auto_ci rule_icmp_23

/-- `icmp.isle:25`. -/
theorem ok_rule_icmp_25 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_25 := by
  first | rule_auto_c rule_icmp_25 | rule_auto_ci rule_icmp_25

/-- `icmp.isle:27`. -/
theorem ok_rule_icmp_27 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_27 := by
  first | rule_auto_c rule_icmp_27 | rule_auto_ci rule_icmp_27

/-- `icmp.isle:29`. -/
theorem ok_rule_icmp_29 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_29 := by
  first | rule_auto_c rule_icmp_29 | rule_auto_ci rule_icmp_29

/-- `icmp.isle:31`. -/
theorem ok_rule_icmp_31 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_31 := by
  first | rule_auto_c rule_icmp_31 | rule_auto_ci rule_icmp_31

end Opt.Proof
