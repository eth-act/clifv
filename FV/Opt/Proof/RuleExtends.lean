import FV.Opt.Proof.RuleExtEmbed

/-!
# `opts/extends.isle`: proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleExtEmbed.lean`); a `first` chain lists the templates the rule was checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000


/-- `extends.isle:2`. -/
theorem ok_rule_extends_2 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_2 := by
  first | rule_auto rule_extends_2 | rule_auto_b rule_extends_2 | rule_auto_i rule_extends_2 | rule_auto_z rule_extends_2

/-- `extends.isle:4`. -/
theorem ok_rule_extends_4 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_4 := by
  first | rule_auto rule_extends_4 | rule_auto_b rule_extends_4 | rule_auto_i rule_extends_4 | rule_auto_z rule_extends_4

/-- `extends.isle:8`. -/
theorem ok_rule_extends_8 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_8 := by
  first | rule_auto rule_extends_8 | rule_auto_b rule_extends_8 | rule_auto_i rule_extends_8 | rule_auto_z rule_extends_8

/-- `extends.isle:12`. -/
theorem ok_rule_extends_12 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_12 := by
  first | rule_auto rule_extends_12 | rule_auto_b rule_extends_12 | rule_auto_i rule_extends_12 | rule_auto_z rule_extends_12

/-- `extends.isle:17`. -/
theorem ok_rule_extends_17 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_17 := by
  rule_auto_xz rule_extends_17

/-- `extends.isle:23`. -/
theorem ok_rule_extends_23 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_23 := by
  rule_auto_xz rule_extends_23

/-- `extends.isle:28`. -/
theorem ok_rule_extends_28 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_28 := by
  first | rule_auto rule_extends_28 | rule_auto_b rule_extends_28 | rule_auto_i rule_extends_28 | rule_auto_z rule_extends_28

/-- `extends.isle:33`. -/
theorem ok_rule_extends_33 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_33 := by
  first | rule_auto rule_extends_33 | rule_auto_b rule_extends_33 | rule_auto_i rule_extends_33 | rule_auto_z rule_extends_33

/-- `extends.isle:50`. -/
theorem ok_rule_extends_50 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_50 := by
  first | rule_auto rule_extends_50 | rule_auto_b rule_extends_50 | rule_auto_i rule_extends_50 | rule_auto_z rule_extends_50

/-- `extends.isle:51`. -/
theorem ok_rule_extends_51 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_51 := by
  first | rule_auto rule_extends_51 | rule_auto_b rule_extends_51 | rule_auto_i rule_extends_51 | rule_auto_z rule_extends_51

/-- `extends.isle:55`. -/
theorem ok_rule_extends_55 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_55 := by
  first | rule_auto rule_extends_55 | rule_auto_b rule_extends_55 | rule_auto_i rule_extends_55 | rule_auto_z rule_extends_55

/-- `extends.isle:58`. -/
theorem ok_rule_extends_58 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_58 := by
  first | rule_auto rule_extends_58 | rule_auto_b rule_extends_58 | rule_auto_i rule_extends_58 | rule_auto_z rule_extends_58

/-- `extends.isle:62`. -/
theorem ok_rule_extends_62 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_62 := by
  first | rule_auto rule_extends_62 | rule_auto_b rule_extends_62 | rule_auto_i rule_extends_62 | rule_auto_z rule_extends_62

/-- `extends.isle:65`. -/
theorem ok_rule_extends_65 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_65 := by
  first | rule_auto rule_extends_65 | rule_auto_b rule_extends_65 | rule_auto_i rule_extends_65 | rule_auto_z rule_extends_65

/-- `extends.isle:71`. -/
theorem ok_rule_extends_71 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_71 := by
  rule_auto_x rule_extends_71

/-- `extends.isle:73`. -/
theorem ok_rule_extends_73 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_73 := by
  first | rule_auto_xr rule_extends_73 | rule_auto_xz rule_extends_73

/-- `extends.isle:75`. -/
theorem ok_rule_extends_75 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_75 := by
  first | rule_auto_xr rule_extends_75 | rule_auto_xz rule_extends_75

/-- `extends.isle:83`. -/
theorem ok_rule_extends_83 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_83 := by
  first | rule_auto rule_extends_83 | rule_auto_b rule_extends_83 | rule_auto_i rule_extends_83 | rule_auto_z rule_extends_83

/-- `extends.isle:84`. -/
theorem ok_rule_extends_84 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_84 := by
  first | rule_auto rule_extends_84 | rule_auto_b rule_extends_84 | rule_auto_i rule_extends_84 | rule_auto_z rule_extends_84

/-- `extends.isle:86`. -/
theorem ok_rule_extends_86 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_86 := by
  rule_auto_x rule_extends_86

/-- `extends.isle:87`. -/
theorem ok_rule_extends_87 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_87 := by
  first | rule_auto_xr rule_extends_87 | rule_auto_xz rule_extends_87

/-- `extends.isle:88`. -/
theorem ok_rule_extends_88 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_88 := by
  first | rule_auto_xr rule_extends_88 | rule_auto_xz rule_extends_88

/-- `extends.isle:89`. -/
theorem ok_rule_extends_89 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_89 := by
  first | rule_auto_xr rule_extends_89 | rule_auto_xz rule_extends_89

/-- `extends.isle:90`. -/
theorem ok_rule_extends_90 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_90 := by
  first | rule_auto_xr rule_extends_90 | rule_auto_xz rule_extends_90

/-- `extends.isle:91`. -/
theorem ok_rule_extends_91 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_91 := by
  first | rule_auto_xr rule_extends_91 | rule_auto_xz rule_extends_91

/-- `extends.isle:98`. -/
theorem ok_rule_extends_98 {p : Isle.Program} (hd : Data p) : RuleOk p rule_extends_98 := by
  first | rule_auto rule_extends_98 | rule_auto_b rule_extends_98 | rule_auto_i rule_extends_98 | rule_auto_z rule_extends_98

end Opt.Proof
