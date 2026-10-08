import FV.Opt.Proof.RuleInfraAbs

/-!
# `opts/selects.isle` (part 7): `select` against 0 to `iabs`

Each rule by the template that closes it (`RuleInfraAbs.lean`).
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000 in
/-- `selects.isle:97`. -/
theorem ok_rule_selects_97 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_97 := by
  rule_auto_a rule_selects_97

set_option maxHeartbeats 4000000 in
/-- `selects.isle:98`. -/
theorem ok_rule_selects_98 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_98 := by
  rule_auto_a rule_selects_98

set_option maxHeartbeats 4000000 in
/-- `selects.isle:99`. -/
theorem ok_rule_selects_99 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_99 := by
  rule_auto_a rule_selects_99

set_option maxHeartbeats 4000000 in
/-- `selects.isle:100`. -/
theorem ok_rule_selects_100 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_100 := by
  rule_auto_a rule_selects_100

end Opt.Proof
