import FV.Opt.Proof.RuleInfraI128

/-!
# `opts/icmp.isle` (part 12): 128-bit comparisons from 64-bit halves

`select (eq hi_a hi_b) (cc_lo lo_a lo_b) (cc hi_a hi_b)` to `cc` of two `iconcat`s, by
`rule_auto_i128cmp` (`RuleInfraI128.lean`). Theorems are elaborated one at a time
(`Elab.async false`): in parallel they exceed the memory cap.
-/

set_option Elab.async false
set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000 in
/-- `icmp.isle:254`. -/
theorem ok_rule_icmp_254 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_254 := by
  rule_auto_i128cmp rule_icmp_254

set_option maxHeartbeats 4000000 in
/-- `icmp.isle:259`. -/
theorem ok_rule_icmp_259 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_259 := by
  rule_auto_i128cmp rule_icmp_259

set_option maxHeartbeats 4000000 in
/-- `icmp.isle:264`. -/
theorem ok_rule_icmp_264 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_264 := by
  rule_auto_i128cmp rule_icmp_264

set_option maxHeartbeats 4000000 in
/-- `icmp.isle:269`. -/
theorem ok_rule_icmp_269 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_269 := by
  rule_auto_i128cmp rule_icmp_269

end Opt.Proof
