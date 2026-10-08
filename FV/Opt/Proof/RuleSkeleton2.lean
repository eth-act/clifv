import FV.Opt.Proof.RuleInfraPow2

/-!
# Proven `simplify_skeleton` rules (part 2): division by a power of two

`SkelRuleOk` for the power-of-two `udiv`/`sdiv`/`urem`/`srem` rewrites of `arithmetic.isle`
(83, 87, 102, 135) and `skeleton.isle` 80 (142: `RuleSkeleton4.lean`), by `pow2_auto_div`
(`FV/Opt/Proof/RuleInfraPow2.lean`): the divisor's immediate becomes `± 2 ^ k`, the helpers
(`u64_ilog2`, `*_trailing_zeros`, `u32_sub`, `iconst_u`/`iconst_s`, …) evaluate on it, and the
shift sequence is closed by a bit-level lemma (`pow2_*_seq`, decided per width with the
exponent as a bit vector).
-/

set_option linter.unusedSimpArgs false
set_option Elab.async false

namespace Opt.Proof

open Isle Isle.Opt Isle.Interp Clif

set_option maxHeartbeats 16000000 in
theorem ok_rule_arithmetic_83 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_arithmetic_83 := by
  pow2_auto_div rule_arithmetic_83 using exact pow2_udiv_seq (by omega) _

set_option maxHeartbeats 16000000 in
theorem ok_rule_arithmetic_87 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_arithmetic_87 := by
  pow2_auto_div rule_arithmetic_87 using exact pow2_sdiv_seq ‹_› (by omega) (by omega) _

set_option maxHeartbeats 16000000 in
theorem ok_rule_arithmetic_102 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_arithmetic_102 := by
  pow2_auto_div rule_arithmetic_102 using exact pow2_sdiv_neg_seq ‹_› (by omega) (by omega) _

set_option maxHeartbeats 16000000 in
theorem ok_rule_arithmetic_135 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_arithmetic_135 := by
  pow2_auto_div rule_arithmetic_135 using exact pow2_urem_seq (by omega) _

set_option maxHeartbeats 16000000 in
theorem ok_rule_skeleton_80 {p : Isle.Program} (hd : Data p) : SkelRuleOk p rule_skeleton_80 := by
  pow2_auto_div rule_skeleton_80 using exact pow2_udiv_select_seq (by omega) (by omega) _ _

end Opt.Proof
