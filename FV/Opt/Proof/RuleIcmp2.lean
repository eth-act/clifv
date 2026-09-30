import FV.Opt.Proof.RuleIcmpEmbed2

/-!
# `opts/icmp.isle` (part 2): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleIcmpEmbed.lean`, `RuleIcmpEmbed2.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `icmp.isle:33`. -/
theorem ok_rule_icmp_33 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_33 := by
  first | rule_auto_c rule_icmp_33 | rule_auto_ci rule_icmp_33

/-- `icmp.isle:35`. -/
theorem ok_rule_icmp_35 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_35 := by
  first | rule_auto_c rule_icmp_35 | rule_auto_ci rule_icmp_35

/-- `icmp.isle:41`. -/
theorem ok_rule_icmp_41 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_41 := by
  first | rule_auto rule_icmp_41 | rule_auto_b rule_icmp_41 | rule_auto_i rule_icmp_41 | rule_auto_z rule_icmp_41

/-- `icmp.isle:43`. -/
theorem ok_rule_icmp_43 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_43 := by
  first | rule_auto rule_icmp_43 | rule_auto_b rule_icmp_43 | rule_auto_i rule_icmp_43 | rule_auto_z rule_icmp_43

/-- `icmp.isle:49`. -/
theorem ok_rule_icmp_49 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_49 := by
  rule_auto_f rule_icmp_49

/-- `icmp.isle:63`. -/
theorem ok_rule_icmp_63 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_63 := by
  rule_auto_f rule_icmp_63

set_option maxHeartbeats 16000000 in
/-- `icmp.isle:70`. -/
theorem ok_rule_icmp_70 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_70 := by
  first | rule_auto_f rule_icmp_70 [tySmin_ofClif, tySmax_ofClif] | rule_auto_fi rule_icmp_70 [tySmin_ofClif, tySmax_ofClif] | rule_auto_fz rule_icmp_70 [tySmin_ofClif, tySmax_ofClif] | rule_auto_fiz rule_icmp_70 [tySmin_ofClif, tySmax_ofClif]

set_option maxHeartbeats 16000000 in
/-- `icmp.isle:77`. -/
theorem ok_rule_icmp_77 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_77 := by
  first | rule_auto_f rule_icmp_77 [tySmin_ofClif, tySmax_ofClif] | rule_auto_fi rule_icmp_77 [tySmin_ofClif, tySmax_ofClif] | rule_auto_fz rule_icmp_77 [tySmin_ofClif, tySmax_ofClif] | rule_auto_fiz rule_icmp_77 [tySmin_ofClif, tySmax_ofClif]

/-- `icmp.isle:84`. -/
theorem ok_rule_icmp_84 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_84 := by
  first | rule_auto rule_icmp_84 | rule_auto_b rule_icmp_84 | rule_auto_i rule_icmp_84 | rule_auto_z rule_icmp_84

/-- `icmp.isle:91`. -/
theorem ok_rule_icmp_91 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_91 := by
  rule_auto_g rule_icmp_91

/-- `icmp.isle:96`. -/
theorem ok_rule_icmp_96 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_96 := by
  first | rule_auto rule_icmp_96 | rule_auto_b rule_icmp_96 | rule_auto_i rule_icmp_96 | rule_auto_z rule_icmp_96

/-- `icmp.isle:104`. -/
theorem ok_rule_icmp_104 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_104 := by
  first | rule_auto rule_icmp_104 | rule_auto_b rule_icmp_104 | rule_auto_i rule_icmp_104 | rule_auto_z rule_icmp_104

/-- `icmp.isle:108`. -/
theorem ok_rule_icmp_108 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_108 := by
  first | rule_auto rule_icmp_108 | rule_auto_b rule_icmp_108 | rule_auto_i rule_icmp_108 | rule_auto_z rule_icmp_108

/-- `icmp.isle:112`. -/
theorem ok_rule_icmp_112 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_112 := by
  first | rule_auto rule_icmp_112 | rule_auto_b rule_icmp_112 | rule_auto_i rule_icmp_112 | rule_auto_z rule_icmp_112

/-- `icmp.isle:116`. -/
theorem ok_rule_icmp_116 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_116 := by
  first | rule_auto rule_icmp_116 | rule_auto_b rule_icmp_116 | rule_auto_i rule_icmp_116 | rule_auto_z rule_icmp_116

/-- `icmp.isle:120`. -/
theorem ok_rule_icmp_120 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_120 := by
  first | rule_auto_d rule_icmp_120 [tySmin_ofClif, tySmax_ofClif] | rule_auto_di rule_icmp_120 [tySmin_ofClif, tySmax_ofClif]

end Opt.Proof
