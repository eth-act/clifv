import FV.Opt.Proof.RuleIcmpEmbed2

/-!
# `opts/icmp.isle` (part 3): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleIcmpEmbed.lean`, `RuleIcmpEmbed2.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `icmp.isle:125`. -/
theorem ok_rule_icmp_125 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_125 := by
  first | rule_auto_d rule_icmp_125 [tySmin_ofClif, tySmax_ofClif] | rule_auto_di rule_icmp_125 [tySmin_ofClif, tySmax_ofClif]

/-- `icmp.isle:130`. -/
theorem ok_rule_icmp_130 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_130 := by
  first | rule_auto_d rule_icmp_130 [tySmin_ofClif, tySmax_ofClif] | rule_auto_di rule_icmp_130 [tySmin_ofClif, tySmax_ofClif]

/-- `icmp.isle:135`. -/
theorem ok_rule_icmp_135 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_135 := by
  first | rule_auto_d rule_icmp_135 [tySmin_ofClif, tySmax_ofClif] | rule_auto_di rule_icmp_135 [tySmin_ofClif, tySmax_ofClif]

/-- `icmp.isle:140`. -/
theorem ok_rule_icmp_140 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_140 := by
  first | rule_auto_d rule_icmp_140 [tySmin_ofClif, tySmax_ofClif] | rule_auto_di rule_icmp_140 [tySmin_ofClif, tySmax_ofClif]

/-- `icmp.isle:145`. -/
theorem ok_rule_icmp_145 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_145 := by
  first | rule_auto_d rule_icmp_145 [tySmin_ofClif, tySmax_ofClif] | rule_auto_di rule_icmp_145 [tySmin_ofClif, tySmax_ofClif]

/-- `icmp.isle:150`. -/
theorem ok_rule_icmp_150 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_150 := by
  first | rule_auto_d rule_icmp_150 [tySmin_ofClif, tySmax_ofClif] | rule_auto_di rule_icmp_150 [tySmin_ofClif, tySmax_ofClif]

/-- `icmp.isle:190`. -/
theorem ok_rule_icmp_190 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_190 := by
  first | rule_auto rule_icmp_190 | rule_auto_b rule_icmp_190 | rule_auto_i rule_icmp_190 | rule_auto_z rule_icmp_190

/-- `icmp.isle:193`. -/
theorem ok_rule_icmp_193 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_193 := by
  first | rule_auto rule_icmp_193 | rule_auto_b rule_icmp_193 | rule_auto_i rule_icmp_193 | rule_auto_z rule_icmp_193

end Opt.Proof
