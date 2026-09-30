import FV.Opt.Proof.RuleIcmpEmbed2

/-!
# `opts/selects.isle` (part 3): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleIcmpEmbed.lean`, `RuleIcmpEmbed2.lean`); a `first` chain lists the templates the rule was
checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000

/-- `selects.isle:116`. -/
theorem ok_rule_selects_116 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_116 := by
  first | rule_auto rule_selects_116 | rule_auto_b rule_selects_116 | rule_auto_i rule_selects_116 | rule_auto_z rule_selects_116

/-- `selects.isle:117`. -/
theorem ok_rule_selects_117 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_117 := by
  first | rule_auto rule_selects_117 | rule_auto_b rule_selects_117 | rule_auto_i rule_selects_117 | rule_auto_z rule_selects_117

/-- `selects.isle:118`. -/
theorem ok_rule_selects_118 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_118 := by
  first | rule_auto rule_selects_118 | rule_auto_b rule_selects_118 | rule_auto_i rule_selects_118 | rule_auto_z rule_selects_118

/-- `selects.isle:119`. -/
theorem ok_rule_selects_119 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_119 := by
  first | rule_auto rule_selects_119 | rule_auto_b rule_selects_119 | rule_auto_i rule_selects_119 | rule_auto_z rule_selects_119

/-- `selects.isle:120`. -/
theorem ok_rule_selects_120 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_120 := by
  first | rule_auto rule_selects_120 | rule_auto_b rule_selects_120 | rule_auto_i rule_selects_120 | rule_auto_z rule_selects_120

/-- `selects.isle:124`. -/
theorem ok_rule_selects_124 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_124 := by
  first | rule_auto rule_selects_124 | rule_auto_b rule_selects_124 | rule_auto_i rule_selects_124 | rule_auto_z rule_selects_124

/-- `selects.isle:125`. -/
theorem ok_rule_selects_125 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_125 := by
  first | rule_auto rule_selects_125 | rule_auto_b rule_selects_125 | rule_auto_i rule_selects_125 | rule_auto_z rule_selects_125

/-- `selects.isle:126`. -/
theorem ok_rule_selects_126 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_126 := by
  first | rule_auto rule_selects_126 | rule_auto_b rule_selects_126 | rule_auto_i rule_selects_126 | rule_auto_z rule_selects_126

/-- `selects.isle:127`. -/
theorem ok_rule_selects_127 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_127 := by
  first | rule_auto rule_selects_127 | rule_auto_b rule_selects_127 | rule_auto_i rule_selects_127 | rule_auto_z rule_selects_127

/-- `selects.isle:130`. -/
theorem ok_rule_selects_130 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_130 := by
  first | rule_auto rule_selects_130 | rule_auto_b rule_selects_130 | rule_auto_i rule_selects_130 | rule_auto_z rule_selects_130

/-- `selects.isle:131`. -/
theorem ok_rule_selects_131 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_131 := by
  first | rule_auto rule_selects_131 | rule_auto_b rule_selects_131 | rule_auto_i rule_selects_131 | rule_auto_z rule_selects_131

/-- `selects.isle:132`. -/
theorem ok_rule_selects_132 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_132 := by
  first | rule_auto rule_selects_132 | rule_auto_b rule_selects_132 | rule_auto_i rule_selects_132 | rule_auto_z rule_selects_132

/-- `selects.isle:133`. -/
theorem ok_rule_selects_133 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_133 := by
  first | rule_auto rule_selects_133 | rule_auto_b rule_selects_133 | rule_auto_i rule_selects_133 | rule_auto_z rule_selects_133

/-- `selects.isle:137`. -/
theorem ok_rule_selects_137 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_137 := by
  first | rule_auto rule_selects_137 | rule_auto_b rule_selects_137 | rule_auto_i rule_selects_137 | rule_auto_z rule_selects_137

end Opt.Proof
