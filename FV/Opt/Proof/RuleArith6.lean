import FV.Opt.Proof.RuleInfraAbs

/-!
# `opts/arithmetic.isle` (part 6): `iabs` and `imul` of negations

Each rule by the template that closes it (`RuleInfraAbs.lean`).
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:38`. -/
theorem ok_rule_arithmetic_38 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_38 := by
  rule_auto_a rule_arithmetic_38

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:42`. -/
theorem ok_rule_arithmetic_42 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_42 := by
  rule_auto_a rule_arithmetic_42

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:46`. -/
theorem ok_rule_arithmetic_46 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_46 := by
  rule_auto_a rule_arithmetic_46

end Opt.Proof
