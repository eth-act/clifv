import FV.Opt.Proof.RuleBitops7P1
import FV.Opt.Proof.RuleBitops7P2
import FV.Opt.Proof.RuleBitops7P3
import FV.Opt.Proof.RuleBitops7P4

/-!
# `opts/bitops.isle` (part 7): proven `simplify` rules that need the bitops template variants

`rule_auto_z` (`FV/Opt/Proof/RuleBitopsEmbed.lean`): right-hand sides built by the internal
constructors `all_zero`, `iconst_s ty -1` and `cmp_true`, whose rules take a different arm at
`i128` (`uextend.i128`/`sextend.i128` of an `i64` constant): the type is split on `i128` first.
`rule_auto_zi` (`RuleIntRetry.lean`) also splits the type on `isInt`: at a float type `iconst_s`
and `cmp_true` have no rule, and `all_zero`'s `$F32`/`$F64` arms call the unmodeled
`f32_from_uint`/`f64_from_uint` (`RuleFloatArms.lean` evaluates those arms).
-/

-- The theorems live in `RuleBitops7P1` .. `RuleBitops7P4` (split to bound the elaboration memory).
