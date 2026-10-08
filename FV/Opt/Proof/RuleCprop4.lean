import FV.Opt.Proof.RuleInfraConst

/-!
# `opts/cprop.isle` (part 4): `isub x (iconst_s ty k)` to `iadd x (iconst ty (imm64_neg ty k))`

`rule_auto_tv` (`RuleInfraConst.lean`) with `imm64Neg_ofInt` for `imm64_neg` of
`imm64 (i64_cast_unsigned k)` (`k` the sign-extended constant, not a presented immediate).
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt

set_option maxHeartbeats 4000000 in
/-- `cprop.isle:269`. -/
theorem ok_rule_cprop_269 {p : Isle.Program} (hd : Data p) : RuleOk p rule_cprop_269 := by
  rule_auto_tv rule_cprop_269 [imm64Neg_ofInt, asI64_asU64_cast, ofInt_asI64_low, BitVec.ofInt_toInt]

end Opt.Proof
