import FV.Opt.Proof.RuleInfraAbs

/-!
# `opts/bitops.isle` (part 8): conditions stripped by `truthy`

Each rule by the template that closes it (`RuleInfraAbs.lean`).
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000 in
/-- `bitops.isle:126`. -/
theorem ok_rule_bitops_126 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_126 := by
  rule_auto_t rule_bitops_126

set_option maxHeartbeats 4000000 in
/-- `bitops.isle:127`. -/
theorem ok_rule_bitops_127 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_127 := by
  rule_auto_t rule_bitops_127

set_option maxHeartbeats 4000000 in
/-- `bitops.isle:129`. -/
theorem ok_rule_bitops_129 {p : Isle.Program} (hd : Data p) : RuleOk p rule_bitops_129 := by
  rule_auto_tt rule_bitops_129

end Opt.Proof
