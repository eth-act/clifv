import FV.Opt.Proof.RuleExtEmbed

/-!
# `opts/spaceship.isle`: proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleExtEmbed.lean`); a `first` chain lists the templates the rule was checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000


/-- `spaceship.isle:146`. -/
theorem ok_rule_spaceship_146 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_146 := by
  rule_auto_xr rule_spaceship_146

/-- `spaceship.isle:148`. -/
theorem ok_rule_spaceship_148 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_148 := by
  rule_auto_xr rule_spaceship_148

/-- `spaceship.isle:151`. -/
theorem ok_rule_spaceship_151 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_151 := by
  rule_auto_xr rule_spaceship_151

/-- `spaceship.isle:153`. -/
theorem ok_rule_spaceship_153 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_153 := by
  rule_auto_xr rule_spaceship_153

/-- `spaceship.isle:157`. -/
theorem ok_rule_spaceship_157 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_157 := by
  rule_auto_xr rule_spaceship_157

/-- `spaceship.isle:159`. -/
theorem ok_rule_spaceship_159 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_159 := by
  rule_auto_xr rule_spaceship_159

/-- `spaceship.isle:162`. -/
theorem ok_rule_spaceship_162 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_162 := by
  rule_auto_xr rule_spaceship_162

/-- `spaceship.isle:164`. -/
theorem ok_rule_spaceship_164 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_164 := by
  rule_auto_xr rule_spaceship_164

/-- `spaceship.isle:167`. -/
theorem ok_rule_spaceship_167 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_167 := by
  rule_auto_xr rule_spaceship_167

/-- `spaceship.isle:169`. -/
theorem ok_rule_spaceship_169 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_169 := by
  rule_auto_xr rule_spaceship_169

/-- `spaceship.isle:172`. -/
theorem ok_rule_spaceship_172 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_172 := by
  rule_auto_xr rule_spaceship_172

/-- `spaceship.isle:174`. -/
theorem ok_rule_spaceship_174 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_174 := by
  rule_auto_xr rule_spaceship_174

/-- `spaceship.isle:179`. -/
theorem ok_rule_spaceship_179 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_179 := by
  first | rule_auto rule_spaceship_179 | rule_auto_b rule_spaceship_179 | rule_auto_i rule_spaceship_179 | rule_auto_z rule_spaceship_179

/-- `spaceship.isle:181`. -/
theorem ok_rule_spaceship_181 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_181 := by
  first | rule_auto rule_spaceship_181 | rule_auto_b rule_spaceship_181 | rule_auto_i rule_spaceship_181 | rule_auto_z rule_spaceship_181

/-- `spaceship.isle:183`. -/
theorem ok_rule_spaceship_183 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_183 := by
  first | rule_auto rule_spaceship_183 | rule_auto_b rule_spaceship_183 | rule_auto_i rule_spaceship_183 | rule_auto_z rule_spaceship_183

/-- `spaceship.isle:185`. -/
theorem ok_rule_spaceship_185 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_185 := by
  first | rule_auto rule_spaceship_185 | rule_auto_b rule_spaceship_185 | rule_auto_i rule_spaceship_185 | rule_auto_z rule_spaceship_185

/-- `spaceship.isle:187`. -/
theorem ok_rule_spaceship_187 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_187 := by
  rule_auto_xr rule_spaceship_187

/-- `spaceship.isle:189`. -/
theorem ok_rule_spaceship_189 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_189 := by
  rule_auto_xr rule_spaceship_189

/-- `spaceship.isle:191`. -/
theorem ok_rule_spaceship_191 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_191 := by
  rule_auto_xr rule_spaceship_191

/-- `spaceship.isle:193`. -/
theorem ok_rule_spaceship_193 {p : Isle.Program} (hd : Data p) : RuleOk p rule_spaceship_193 := by
  rule_auto_xr rule_spaceship_193

end Opt.Proof
