import FV.Opt.Proof.RuleInfraPow2

/-!
# Proven `simplify_skeleton` rules (part 4): `srem` by `± 2 ^ k`

`arithmetic.isle` 142 by `pow2_auto_div` (`FV/Opt/Proof/RuleInfraPow2.lean`), in a module of its
own (its three branches — `2 ^ k`, `i64::MIN`, `-2 ^ k` — make it the heaviest skeleton rule).
-/

set_option linter.unusedSimpArgs false
set_option Elab.async false

namespace Opt.Proof

open Isle Isle.Opt Isle.Interp Clif

set_option maxHeartbeats 16000000 in
theorem ok_rule_arithmetic_142 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_arithmetic_142 := by
  pow2_auto_div rule_arithmetic_142 using first
    | (pow2_neg_goal; exact pow2_srem_neg_seq ‹_› (by omega) (by omega) _)
    | exact pow2_srem_pos_seq ‹_› (by omega) (by omega) _

end Opt.Proof
