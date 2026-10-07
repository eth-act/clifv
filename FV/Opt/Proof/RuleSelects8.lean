import FV.Opt.Proof.RuleInfraIcmp

/-!
# `opts/selects.isle` (part 8): `select` of an `icmp` between -1 and 0

Each rule by `rule_pre_k` and the finisher that closes it (`RuleInfraIcmp.lean`).
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000 in
/-- `selects.isle:20`. -/
theorem ok_rule_selects_20 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_20 := by
  rule_pre_k rule_selects_20
  all_goals fin_sel_bmask_k

end Opt.Proof
