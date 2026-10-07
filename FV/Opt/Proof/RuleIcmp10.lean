import FV.Opt.Proof.RuleInfraIcmp

/-!
# `opts/icmp.isle` (part 10): rules whose earlier proofs ran out of memory

Each rule by `rule_pre_k` and the finisher that closes it (`RuleInfraIcmp.lean`).
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000 in
/-- `icmp.isle:63`. -/
theorem ok_rule_icmp_63 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_63 := by
  rule_pre_k rule_icmp_63
  all_goals fin_icmp_not_k

set_option maxHeartbeats 4000000 in
/-- `icmp.isle:70`. -/
theorem ok_rule_icmp_70 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_70 := by
  rule_pre_k rule_icmp_70
  all_goals fin_icmp_not_k

set_option maxHeartbeats 4000000 in
/-- `icmp.isle:160`. -/
theorem ok_rule_icmp_160 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_160 := by
  rule_pre_k rule_icmp_160 [tySmin_ofClif, tySmax_ofClif]
  all_goals fin_bits_k

set_option maxHeartbeats 4000000 in
/-- `icmp.isle:175`. -/
theorem ok_rule_icmp_175 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_175 := by
  rule_pre_k rule_icmp_175 [tySmin_ofClif, tySmax_ofClif]
  all_goals fin_bits_k

set_option maxHeartbeats 4000000 in
/-- `icmp.isle:365`. -/
theorem ok_rule_icmp_365 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_365 := by
  rule_pre_k rule_icmp_365
  all_goals fin_bits_k

set_option maxHeartbeats 4000000 in
/-- `icmp.isle:368`. -/
theorem ok_rule_icmp_368 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_368 := by
  rule_pre_k rule_icmp_368
  all_goals fin_bits_k

end Opt.Proof
