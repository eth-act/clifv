import FV.Opt.Proof.RuleIcmpEmbed2

/-!
# `opts/selects.isle` (part 5): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleIcmpEmbed.lean`, `RuleIcmpEmbed2.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `selects.isle:155`. -/
theorem ok_rule_selects_155 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_155 := by
  first | rule_auto rule_selects_155 | rule_auto_b rule_selects_155 | rule_auto_i rule_selects_155 | rule_auto_z rule_selects_155

/-- `selects.isle:159`. -/
theorem ok_rule_selects_159 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_159 := by
  first | rule_auto rule_selects_159 | rule_auto_b rule_selects_159 | rule_auto_i rule_selects_159 | rule_auto_z rule_selects_159

/-- `selects.isle:160`. -/
theorem ok_rule_selects_160 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_160 := by
  first | rule_auto rule_selects_160 | rule_auto_b rule_selects_160 | rule_auto_i rule_selects_160 | rule_auto_z rule_selects_160

/-- `selects.isle:161`. -/
theorem ok_rule_selects_161 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_161 := by
  first | rule_auto rule_selects_161 | rule_auto_b rule_selects_161 | rule_auto_i rule_selects_161 | rule_auto_z rule_selects_161

/-- `selects.isle:162`. -/
theorem ok_rule_selects_162 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_162 := by
  first | rule_auto rule_selects_162 | rule_auto_b rule_selects_162 | rule_auto_i rule_selects_162 | rule_auto_z rule_selects_162

/-- `selects.isle:163`. -/
theorem ok_rule_selects_163 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_163 := by
  first | rule_auto rule_selects_163 | rule_auto_b rule_selects_163 | rule_auto_i rule_selects_163 | rule_auto_z rule_selects_163

/-- `selects.isle:164`. -/
theorem ok_rule_selects_164 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_164 := by
  first | rule_auto rule_selects_164 | rule_auto_b rule_selects_164 | rule_auto_i rule_selects_164 | rule_auto_z rule_selects_164

/-- `selects.isle:165`. -/
theorem ok_rule_selects_165 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_165 := by
  first | rule_auto rule_selects_165 | rule_auto_b rule_selects_165 | rule_auto_i rule_selects_165 | rule_auto_z rule_selects_165

/-- `selects.isle:166`. -/
theorem ok_rule_selects_166 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_166 := by
  first | rule_auto rule_selects_166 | rule_auto_b rule_selects_166 | rule_auto_i rule_selects_166 | rule_auto_z rule_selects_166

/-- `selects.isle:170`. -/
theorem ok_rule_selects_170 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_170 := by
  first | rule_auto rule_selects_170 | rule_auto_b rule_selects_170 | rule_auto_i rule_selects_170 | rule_auto_z rule_selects_170

/-- `selects.isle:171`. -/
theorem ok_rule_selects_171 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_171 := by
  first | rule_auto rule_selects_171 | rule_auto_b rule_selects_171 | rule_auto_i rule_selects_171 | rule_auto_z rule_selects_171

/-- `selects.isle:172`. -/
theorem ok_rule_selects_172 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_172 := by
  first | rule_auto rule_selects_172 | rule_auto_b rule_selects_172 | rule_auto_i rule_selects_172 | rule_auto_z rule_selects_172

/-- `selects.isle:173`. -/
theorem ok_rule_selects_173 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_173 := by
  first | rule_auto rule_selects_173 | rule_auto_b rule_selects_173 | rule_auto_i rule_selects_173 | rule_auto_z rule_selects_173

/-- `selects.isle:174`. -/
theorem ok_rule_selects_174 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_174 := by
  first | rule_auto rule_selects_174 | rule_auto_b rule_selects_174 | rule_auto_i rule_selects_174 | rule_auto_z rule_selects_174

end Opt.Proof
