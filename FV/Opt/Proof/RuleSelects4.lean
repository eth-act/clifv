import FV.Opt.Proof.RuleIcmpEmbed2

/-!
# `opts/selects.isle` (part 4): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleIcmpEmbed.lean`, `RuleIcmpEmbed2.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `selects.isle:138`. -/
theorem ok_rule_selects_138 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_138 := by
  first | rule_auto rule_selects_138 | rule_auto_b rule_selects_138 | rule_auto_i rule_selects_138 | rule_auto_z rule_selects_138

/-- `selects.isle:139`. -/
theorem ok_rule_selects_139 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_139 := by
  first | rule_auto rule_selects_139 | rule_auto_b rule_selects_139 | rule_auto_i rule_selects_139 | rule_auto_z rule_selects_139

/-- `selects.isle:140`. -/
theorem ok_rule_selects_140 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_140 := by
  first | rule_auto rule_selects_140 | rule_auto_b rule_selects_140 | rule_auto_i rule_selects_140 | rule_auto_z rule_selects_140

/-- `selects.isle:141`. -/
theorem ok_rule_selects_141 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_141 := by
  first | rule_auto rule_selects_141 | rule_auto_b rule_selects_141 | rule_auto_i rule_selects_141 | rule_auto_z rule_selects_141

/-- `selects.isle:142`. -/
theorem ok_rule_selects_142 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_142 := by
  first | rule_auto rule_selects_142 | rule_auto_b rule_selects_142 | rule_auto_i rule_selects_142 | rule_auto_z rule_selects_142

/-- `selects.isle:143`. -/
theorem ok_rule_selects_143 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_143 := by
  first | rule_auto rule_selects_143 | rule_auto_b rule_selects_143 | rule_auto_i rule_selects_143 | rule_auto_z rule_selects_143

/-- `selects.isle:144`. -/
theorem ok_rule_selects_144 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_144 := by
  first | rule_auto rule_selects_144 | rule_auto_b rule_selects_144 | rule_auto_i rule_selects_144 | rule_auto_z rule_selects_144

/-- `selects.isle:148`. -/
theorem ok_rule_selects_148 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_148 := by
  first | rule_auto rule_selects_148 | rule_auto_b rule_selects_148 | rule_auto_i rule_selects_148 | rule_auto_z rule_selects_148

/-- `selects.isle:149`. -/
theorem ok_rule_selects_149 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_149 := by
  first | rule_auto rule_selects_149 | rule_auto_b rule_selects_149 | rule_auto_i rule_selects_149 | rule_auto_z rule_selects_149

/-- `selects.isle:150`. -/
theorem ok_rule_selects_150 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_150 := by
  first | rule_auto rule_selects_150 | rule_auto_b rule_selects_150 | rule_auto_i rule_selects_150 | rule_auto_z rule_selects_150

/-- `selects.isle:151`. -/
theorem ok_rule_selects_151 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_151 := by
  first | rule_auto rule_selects_151 | rule_auto_b rule_selects_151 | rule_auto_i rule_selects_151 | rule_auto_z rule_selects_151

/-- `selects.isle:152`. -/
theorem ok_rule_selects_152 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_152 := by
  first | rule_auto rule_selects_152 | rule_auto_b rule_selects_152 | rule_auto_i rule_selects_152 | rule_auto_z rule_selects_152

/-- `selects.isle:153`. -/
theorem ok_rule_selects_153 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_153 := by
  first | rule_auto rule_selects_153 | rule_auto_b rule_selects_153 | rule_auto_i rule_selects_153 | rule_auto_z rule_selects_153

/-- `selects.isle:154`. -/
theorem ok_rule_selects_154 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_154 := by
  first | rule_auto rule_selects_154 | rule_auto_b rule_selects_154 | rule_auto_i rule_selects_154 | rule_auto_z rule_selects_154

end Opt.Proof
