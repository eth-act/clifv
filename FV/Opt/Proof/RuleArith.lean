import FV.Opt.Proof.RuleAuto

/-!
# `opts/arithmetic.isle`: proven `simplify` rules (first batch)

Each theorem is the batching template `rule_auto` (`FV/Opt/Proof/RuleAuto.lean`) on the rule's
data, for an abstract program with `Data p`; the types `i8`..`i128` are all covered (the
identities hold at every width).
-/

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 1000000

/-- `iadd_x_plus_zero`: `x + 0 ⇒ x` (`arithmetic.isle:8`). -/
theorem ok_rule_arithmetic_8 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_8 := by
  rule_auto rule_arithmetic_8

/-- `x - 0 ⇒ x` (`arithmetic.isle:13`). -/
theorem ok_rule_arithmetic_13 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_13 := by
  rule_auto rule_arithmetic_13

/-- `arithmetic.isle:35`. -/
theorem ok_rule_arithmetic_35 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_35 := by
  rule_auto rule_arithmetic_35

/-- `arithmetic.isle:59`. -/
theorem ok_rule_arithmetic_59 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_59 := by
  rule_auto rule_arithmetic_59

end Opt.Proof
