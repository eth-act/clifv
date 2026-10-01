import FV.Opt.Proof.RuleIcmpEmbed2

/-!
# `opts/selects.isle` (part 6): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleIcmpEmbed.lean`, `RuleIcmpEmbed2.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `selects.isle:175`. -/
theorem ok_rule_selects_175 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_175 := by
  first | rule_auto rule_selects_175 | rule_auto_b rule_selects_175 | rule_auto_i rule_selects_175 | rule_auto_z rule_selects_175

/-- `selects.isle:176`. -/
theorem ok_rule_selects_176 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_176 := by
  first | rule_auto rule_selects_176 | rule_auto_b rule_selects_176 | rule_auto_i rule_selects_176 | rule_auto_z rule_selects_176

/-- `selects.isle:177`. -/
theorem ok_rule_selects_177 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_177 := by
  first | rule_auto rule_selects_177 | rule_auto_b rule_selects_177 | rule_auto_i rule_selects_177 | rule_auto_z rule_selects_177

/-- `selects.isle:178`. -/
theorem ok_rule_selects_178 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_178 := by
  first | rule_auto rule_selects_178 | rule_auto_b rule_selects_178 | rule_auto_i rule_selects_178 | rule_auto_z rule_selects_178

/-- `selects.isle:179`. -/
theorem ok_rule_selects_179 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_179 := by
  first | rule_auto rule_selects_179 | rule_auto_b rule_selects_179 | rule_auto_i rule_selects_179 | rule_auto_z rule_selects_179

/-- `selects.isle:180`. -/
theorem ok_rule_selects_180 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_180 := by
  first | rule_auto rule_selects_180 | rule_auto_b rule_selects_180 | rule_auto_i rule_selects_180 | rule_auto_z rule_selects_180

/-- `selects.isle:181`. -/
theorem ok_rule_selects_181 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_181 := by
  first | rule_auto rule_selects_181 | rule_auto_b rule_selects_181 | rule_auto_i rule_selects_181 | rule_auto_z rule_selects_181

/-- `selects.isle:182`. -/
theorem ok_rule_selects_182 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_182 := by
  first | rule_auto rule_selects_182 | rule_auto_b rule_selects_182 | rule_auto_i rule_selects_182 | rule_auto_z rule_selects_182

/-- `selects.isle:183`. -/
theorem ok_rule_selects_183 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_183 := by
  first | rule_auto rule_selects_183 | rule_auto_b rule_selects_183 | rule_auto_i rule_selects_183 | rule_auto_z rule_selects_183

/-- `selects.isle:184`. -/
theorem ok_rule_selects_184 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_184 := by
  first | rule_auto rule_selects_184 | rule_auto_b rule_selects_184 | rule_auto_i rule_selects_184 | rule_auto_z rule_selects_184

/-- `selects.isle:185`. -/
theorem ok_rule_selects_185 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_185 := by
  first | rule_auto rule_selects_185 | rule_auto_b rule_selects_185 | rule_auto_i rule_selects_185 | rule_auto_z rule_selects_185

/-- `selects.isle:205`. -/
theorem ok_rule_selects_205 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_205 := by
  first | rule_auto rule_selects_205 | rule_auto_b rule_selects_205 | rule_auto_i rule_selects_205 | rule_auto_z rule_selects_205

/-- `selects.isle:209`. -/
theorem ok_rule_selects_209 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_209 := by
  first | rule_auto rule_selects_209 | rule_auto_b rule_selects_209 | rule_auto_i rule_selects_209 | rule_auto_z rule_selects_209

/-- `selects.isle:213`. -/
theorem ok_rule_selects_213 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_213 := by
  first | rule_auto rule_selects_213 | rule_auto_b rule_selects_213 | rule_auto_i rule_selects_213 | rule_auto_z rule_selects_213

end Opt.Proof
