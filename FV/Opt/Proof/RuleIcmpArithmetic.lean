import FV.Opt.Proof.RuleInfraIcmp
import FV.Opt.Proof.RuleRestEmbedSshr
import FV.Opt.Proof.RuleRestEmbedRotl
import FV.Opt.Proof.RuleRestEmbedRotr
import FV.Opt.Proof.RuleIntSplit

/-!
# Signed-zero and repeated-operand XOR comparisons

Preserve repeated-operand denotations before evaluating the RHS. The i128 zero
constructor makes an i64 constant and widens it; its width obligation is explicit.
Normalize the signed immediate's Rust mask before bit-blasting, rather than
abstracting that closed zero expression as an unconstrained bit vector. The constants' type
variable is split on `isInt` (`RuleIntSplit.lean`): at a float type the constant has no rule.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option Elab.async false
set_option linter.unusedSimpArgs false

namespace Opt.Proof
open Isle Isle.Opt Clif
attribute [local implicit_reducible] Ty.width

set_option hygiene false in
local macro "icmp_arithmetic_prefix " r:ident : tactic => `(tactic| (
  rule_intro $r
  rule_lhs_g hG
  all_goals rule_no_iflets
  all_goals try opt_den_subst
  all_goals opt_split_i128
  all_goals opt_split_int
  all_goals rule_rhs_y [tyInt_ofClif_notInt]
  all_goals opt_some_subst
  all_goals try opt_den_subst
  all_goals (apply GraphOk.make_val hG (by opt_P); opt_node_x)
  all_goals try decide
  all_goals apply val_congr))

/-- `icmp.isle:205`: signed `x ≤ -1` is `x < 0`. -/
theorem ok_rule_icmp_205 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_205 := by
  icmp_arithmetic_prefix rule_icmp_205
  all_goals simp [Rust.asU64, Rust.asI64, Rust.band64]
  all_goals fin_bits_k

/-- `icmp.isle:295`: equality with one's XOR is a zero test of the other operand. -/
theorem ok_rule_icmp_295 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_295 := by
  icmp_arithmetic_prefix rule_icmp_295
  all_goals fin_bits_k

/-- `icmp.isle:296`: the complementary XOR comparison. -/
theorem ok_rule_icmp_296 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_296 := by
  icmp_arithmetic_prefix rule_icmp_296
  all_goals fin_bits_k

-- The signed literal and both outcomes are inhabited at narrow and wide widths.
example : (255#8).toInt = -1 ∧
    Sem.icmp .sle (128#8) (255#8) = 1#8 ∧ Sem.icmp .slt (128#8) (0#8) = 1#8 ∧
    Sem.icmp .sle (0#8) (255#8) = 0#8 ∧ Sem.icmp .slt (0#8) (0#8) = 0#8 := by decide
example : (0xffffffffffffffff#64).toInt = -1 ∧
    Sem.icmp .sle (0xffffffffffffffff#64) (0xffffffffffffffff#64) = 1#8 ∧
    Sem.icmp .sle (0x7fffffffffffffff#64) (0xffffffffffffffff#64) = 0#8 := by decide

-- Both XOR outcomes, including the i128 RHS's widened-zero construction.
example :
    Sem.icmp .eq (128#8) (Sem.binary .bxor (128#8) (0#8)) = 1#8 ∧
    Sem.icmp .eq (128#8) (Sem.binary .bxor (128#8) (1#8)) = 0#8 := by decide
example :
    Sem.uextend 128 (BitVec.ofInt 64 0) = 0#128 ∧
    Sem.icmp .eq (0#128) (Sem.binary .bxor (0#128) (0#128)) = 1#8 ∧
    Sem.icmp .eq (0#128) (Sem.binary .bxor (0#128) (0x80000000000000000000000000000000#128)) = 0#8 := by decide
example :
    Sem.icmp .ne (255#8) (Sem.binary .bxor (255#8) (0#8)) = 0#8 ∧
    Sem.icmp .ne (255#8) (Sem.binary .bxor (255#8) (128#8)) = 1#8 := by decide
example :
    Sem.icmp .ne (1#128) (Sem.binary .bxor (1#128) (0#128)) = 0#8 ∧
    Sem.icmp .ne (1#128) (Sem.binary .bxor (1#128) (0xffffffffffffffffffffffffffffffff#128)) = 1#8 := by decide

end Opt.Proof
