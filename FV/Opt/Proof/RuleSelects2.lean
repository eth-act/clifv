import FV.Opt.Proof.RuleIcmpEmbed2

/-!
# `opts/selects.isle` (part 2): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleIcmpEmbed.lean`, `RuleIcmpEmbed2.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `selects.isle:38`. -/
theorem ok_rule_selects_38 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_38 := by
  first | rule_auto rule_selects_38 | rule_auto_b rule_selects_38 | rule_auto_i rule_selects_38 | rule_auto_z rule_selects_38

/-- `selects.isle:39`. -/
theorem ok_rule_selects_39 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_39 := by
  first | rule_auto rule_selects_39 | rule_auto_b rule_selects_39 | rule_auto_i rule_selects_39 | rule_auto_z rule_selects_39

/-- `selects.isle:40`. -/
theorem ok_rule_selects_40 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_40 := by
  first | rule_auto rule_selects_40 | rule_auto_b rule_selects_40 | rule_auto_i rule_selects_40 | rule_auto_z rule_selects_40

/-- `selects.isle:41`. -/
theorem ok_rule_selects_41 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_41 := by
  first | rule_auto rule_selects_41 | rule_auto_b rule_selects_41 | rule_auto_i rule_selects_41 | rule_auto_z rule_selects_41

/-- `selects.isle:42`. -/
theorem ok_rule_selects_42 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_42 := by
  first | rule_auto rule_selects_42 | rule_auto_b rule_selects_42 | rule_auto_i rule_selects_42 | rule_auto_z rule_selects_42

/-- `selects.isle:43`. -/
theorem ok_rule_selects_43 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_43 := by
  first | rule_auto rule_selects_43 | rule_auto_b rule_selects_43 | rule_auto_i rule_selects_43 | rule_auto_z rule_selects_43

/-- `selects.isle:91`. -/
theorem ok_rule_selects_91 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_91 := by
  first | rule_auto rule_selects_91 | rule_auto_b rule_selects_91 | rule_auto_i rule_selects_91 | rule_auto_z rule_selects_91

/-- `selects.isle:95`. -/
theorem ok_rule_selects_95 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_95 := by
  first | rule_auto rule_selects_95 | rule_auto_b rule_selects_95 | rule_auto_i rule_selects_95 | rule_auto_z rule_selects_95

/-- `selects.isle:103`. -/
theorem ok_rule_selects_103 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_103 := by
  first | rule_auto rule_selects_103 | rule_auto_b rule_selects_103 | rule_auto_i rule_selects_103 | rule_auto_z rule_selects_103

/-- `selects.isle:109`. -/
theorem ok_rule_selects_109 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_109 := by
  first | rule_auto rule_selects_109 | rule_auto_b rule_selects_109 | rule_auto_i rule_selects_109 | rule_auto_z rule_selects_109

/-- `selects.isle:110`. -/
theorem ok_rule_selects_110 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_110 := by
  first | rule_auto rule_selects_110 | rule_auto_b rule_selects_110 | rule_auto_i rule_selects_110 | rule_auto_z rule_selects_110

/-- `selects.isle:113`. -/
theorem ok_rule_selects_113 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_113 := by
  first | rule_auto rule_selects_113 | rule_auto_b rule_selects_113 | rule_auto_i rule_selects_113 | rule_auto_z rule_selects_113

/-- `selects.isle:114`. -/
theorem ok_rule_selects_114 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_114 := by
  first | rule_auto rule_selects_114 | rule_auto_b rule_selects_114 | rule_auto_i rule_selects_114 | rule_auto_z rule_selects_114

/-- `selects.isle:115`. -/
theorem ok_rule_selects_115 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_115 := by
  first | rule_auto rule_selects_115 | rule_auto_b rule_selects_115 | rule_auto_i rule_selects_115 | rule_auto_z rule_selects_115

end Opt.Proof
