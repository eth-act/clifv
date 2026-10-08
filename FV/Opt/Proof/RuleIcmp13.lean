import FV.Opt.Proof.RuleInfraI128

/-!
# `opts/icmp.isle` (part 13): 128-bit comparisons from 64-bit halves

`select (eq hi_a hi_b) (cc_lo lo_a lo_b) (cc hi_a hi_b)` to `cc` of two `iconcat`s, by
`rule_auto_i128cmp` (`RuleInfraI128.lean`). Theorems are elaborated one at a time
(`Elab.async false`): in parallel they exceed the memory cap.
-/

set_option Elab.async false
set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000 in
/-- `icmp.isle:274`. -/
theorem ok_rule_icmp_274 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_274 := by
  rule_auto_i128cmp rule_icmp_274

set_option maxHeartbeats 4000000 in
/-- `icmp.isle:279`. -/
theorem ok_rule_icmp_279 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_279 := by
  rule_auto_i128cmp rule_icmp_279

set_option maxHeartbeats 4000000 in
/-- `icmp.isle:284`. -/
theorem ok_rule_icmp_284 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_284 := by
  rule_auto_i128cmp rule_icmp_284

set_option maxHeartbeats 4000000 in
/-- `icmp.isle:289`. -/
theorem ok_rule_icmp_289 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_289 := by
  rule_auto_i128cmp rule_icmp_289

end Opt.Proof
