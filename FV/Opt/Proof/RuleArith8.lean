import FV.Opt.Proof.RuleInfraPow2

/-!
# `opts/arithmetic.isle` (part 8): `imul` by a power of two

`arithmetic.isle` 181 (`imul ty x (iconst _ (imm64_power_of_two c))` → `ishl ty x (iconst ty
(imm64 c))`) by `pow2_auto_simp` (`FV/Opt/Proof/RuleInfraPow2.lean`): the matched immediate is
`2 ^ k` (`pow2_imm64PowerOfTwo_ty`; the `iconst` has the `imul`'s type, since the matched `imul`
node has a value), and `x * 2 ^ k = x << k` (`pow2_imul_ishl`).
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000 in
/-- `arithmetic.isle:181`. -/
theorem ok_rule_arithmetic_181 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_181 := by
  pow2_auto_simp rule_arithmetic_181 using exact pow2_imul_ishl (by omega) (by omega) _

end Opt.Proof
