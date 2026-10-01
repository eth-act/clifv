import FV.Opt.Proof.RuleExtEmbed

/-!
# `opts/shifts.isle` (part 1): proven `simplify` rules

Each rule by the template that closes it (`RuleAuto.lean`, `RuleBitopsEmbed.lean`,
`RuleExtEmbed.lean`); a `first` chain lists the templates the rule was checked against, in order.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000


/-- `shifts.isle:4`. -/
theorem ok_rule_shifts_4 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_4 := by
  first | rule_auto rule_shifts_4 | rule_auto_b rule_shifts_4 | rule_auto_i rule_shifts_4 | rule_auto_z rule_shifts_4

/-- `shifts.isle:8`. -/
theorem ok_rule_shifts_8 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_8 := by
  first | rule_auto rule_shifts_8 | rule_auto_b rule_shifts_8 | rule_auto_i rule_shifts_8 | rule_auto_z rule_shifts_8

/-- `shifts.isle:12`. -/
theorem ok_rule_shifts_12 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_12 := by
  first | rule_auto rule_shifts_12 | rule_auto_b rule_shifts_12 | rule_auto_i rule_shifts_12 | rule_auto_z rule_shifts_12

/-- `shifts.isle:16`. -/
theorem ok_rule_shifts_16 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_16 := by
  first | rule_auto rule_shifts_16 | rule_auto_b rule_shifts_16 | rule_auto_i rule_shifts_16 | rule_auto_z rule_shifts_16

/-- `shifts.isle:20`. -/
theorem ok_rule_shifts_20 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_20 := by
  first | rule_auto rule_shifts_20 | rule_auto_b rule_shifts_20 | rule_auto_i rule_shifts_20 | rule_auto_z rule_shifts_20

/-- `shifts.isle:27`. -/
theorem ok_rule_shifts_27 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_27 := by
  first | rule_auto_xr rule_shifts_27 | rule_auto_xz rule_shifts_27

/-- `shifts.isle:32`. -/
theorem ok_rule_shifts_32 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_32 := by
  first | rule_auto_xr rule_shifts_32 | rule_auto_xz rule_shifts_32

/-- `shifts.isle:99`. -/
theorem ok_rule_shifts_99 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_99 := by
  first | rule_auto rule_shifts_99 | rule_auto_b rule_shifts_99 | rule_auto_i rule_shifts_99 | rule_auto_z rule_shifts_99

/-- `shifts.isle:115`. -/
theorem ok_rule_shifts_115 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_115 := by
  first | rule_auto rule_shifts_115 | rule_auto_b rule_shifts_115 | rule_auto_i rule_shifts_115 | rule_auto_z rule_shifts_115

/-- `shifts.isle:116`. -/
theorem ok_rule_shifts_116 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_116 := by
  first | rule_auto rule_shifts_116 | rule_auto_b rule_shifts_116 | rule_auto_i rule_shifts_116 | rule_auto_z rule_shifts_116

/-- `shifts.isle:117`. -/
theorem ok_rule_shifts_117 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_117 := by
  first | rule_auto rule_shifts_117 | rule_auto_b rule_shifts_117 | rule_auto_i rule_shifts_117 | rule_auto_z rule_shifts_117

/-- `shifts.isle:118`. -/
theorem ok_rule_shifts_118 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_118 := by
  first | rule_auto rule_shifts_118 | rule_auto_b rule_shifts_118 | rule_auto_i rule_shifts_118 | rule_auto_z rule_shifts_118

/-- `shifts.isle:119`. -/
theorem ok_rule_shifts_119 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_119 := by
  first | rule_auto rule_shifts_119 | rule_auto_b rule_shifts_119 | rule_auto_i rule_shifts_119 | rule_auto_z rule_shifts_119

/-- `shifts.isle:120`. -/
theorem ok_rule_shifts_120 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_120 := by
  first | rule_auto rule_shifts_120 | rule_auto_b rule_shifts_120 | rule_auto_i rule_shifts_120 | rule_auto_z rule_shifts_120

/-- `shifts.isle:121`. -/
theorem ok_rule_shifts_121 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_121 := by
  first | rule_auto rule_shifts_121 | rule_auto_b rule_shifts_121 | rule_auto_i rule_shifts_121 | rule_auto_z rule_shifts_121

/-- `shifts.isle:122`. -/
theorem ok_rule_shifts_122 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_122 := by
  first | rule_auto rule_shifts_122 | rule_auto_b rule_shifts_122 | rule_auto_i rule_shifts_122 | rule_auto_z rule_shifts_122

/-- `shifts.isle:123`. -/
theorem ok_rule_shifts_123 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_123 := by
  first | rule_auto rule_shifts_123 | rule_auto_b rule_shifts_123 | rule_auto_i rule_shifts_123 | rule_auto_z rule_shifts_123

/-- `shifts.isle:124`. -/
theorem ok_rule_shifts_124 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_124 := by
  first | rule_auto rule_shifts_124 | rule_auto_b rule_shifts_124 | rule_auto_i rule_shifts_124 | rule_auto_z rule_shifts_124

/-- `shifts.isle:125`. -/
theorem ok_rule_shifts_125 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_125 := by
  first | rule_auto rule_shifts_125 | rule_auto_b rule_shifts_125 | rule_auto_i rule_shifts_125 | rule_auto_z rule_shifts_125

/-- `shifts.isle:126`. -/
theorem ok_rule_shifts_126 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_126 := by
  first | rule_auto rule_shifts_126 | rule_auto_b rule_shifts_126 | rule_auto_i rule_shifts_126 | rule_auto_z rule_shifts_126

/-- `shifts.isle:127`. -/
theorem ok_rule_shifts_127 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_127 := by
  first | rule_auto rule_shifts_127 | rule_auto_b rule_shifts_127 | rule_auto_i rule_shifts_127 | rule_auto_z rule_shifts_127

/-- `shifts.isle:128`. -/
theorem ok_rule_shifts_128 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_128 := by
  first | rule_auto rule_shifts_128 | rule_auto_b rule_shifts_128 | rule_auto_i rule_shifts_128 | rule_auto_z rule_shifts_128

/-- `shifts.isle:129`. -/
theorem ok_rule_shifts_129 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_129 := by
  first | rule_auto rule_shifts_129 | rule_auto_b rule_shifts_129 | rule_auto_i rule_shifts_129 | rule_auto_z rule_shifts_129

/-- `shifts.isle:139`. -/
theorem ok_rule_shifts_139 {p : Isle.Program} (hd : Data p) : RuleOk p rule_shifts_139 := by
  rule_auto_cat rule_shifts_139

end Opt.Proof
