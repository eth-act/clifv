import FV.Opt.Proof.RuleInfraIcmp
import FV.Opt.Proof.RuleRestEmbedSshr
import FV.Opt.Proof.RuleRestEmbedRotl
import FV.Opt.Proof.RuleRestEmbedRotr
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace Opt.Proof
open Isle Isle.Opt Clif
attribute [local implicit_reducible] Ty.width

private theorem arith_smax_comm {w : Nat} (x y : BitVec w) : Sem.smax x y = Sem.smax y x := by
  simp only [Sem.smax, BitVec.sle, decide_eq_true_eq]
  split <;> split
  · exact BitVec.toInt_inj.mp (by omega)
  · rfl
  · rfl
  · omega

private theorem arith_umax_comm {w : Nat} (x y : BitVec w) : Sem.umax x y = Sem.umax y x := by
  simp only [Sem.umax, BitVec.ule, decide_eq_true_eq]
  split <;> split
  · exact BitVec.toNat_inj.mp (by omega)
  · rfl
  · rfl
  · omega

private theorem arith_smax_square {w : Nat} (x : BitVec w) :
    Sem.smax (-x) x * Sem.smax (-x) x = x * x := by
  simp only [Sem.smax]
  split <;> simp_all only [ite_true, ite_false, BitVec.neg_mul_neg]

private theorem arith_umax_square {w : Nat} (x : BitVec w) :
    Sem.umax (-x) x * Sem.umax (-x) x = x * x := by
  simp only [Sem.umax]
  split <;> simp_all only [ite_true, ite_false, BitVec.neg_mul_neg]

set_option hygiene false in
local macro "arith_products_prefix " r:ident : tactic => `(tactic| (
  rule_intro $r
  rule_lhs_g hG
  all_goals rule_no_iflets
  all_goals try opt_den_subst
  all_goals rule_rhs_c []
  all_goals opt_some_subst
  all_goals try opt_den_subst
  all_goals (apply GraphOk.make_val hG (by opt_P); opt_node)
  all_goals apply val_congr
  all_goals simp only [Sem.binary, Sem.unary, Sem.imul, Sem.ineg]))

/-- `arithmetic.isle:427`: symbolic modular product identity. -/
theorem ok_rule_arithmetic_427 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_427 := by
  arith_products_prefix rule_arithmetic_427
  all_goals simp only [BitVec.neg_mul, BitVec.mul_neg, BitVec.neg_neg, BitVec.mul_comm]

/-- `arithmetic.isle:428`: symbolic modular product identity. -/
theorem ok_rule_arithmetic_428 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_428 := by
  arith_products_prefix rule_arithmetic_428
  all_goals simp only [BitVec.neg_mul, BitVec.mul_neg, BitVec.neg_neg, BitVec.mul_comm]

/-- `arithmetic.isle:615`: symbolic modular product identity. -/
theorem ok_rule_arithmetic_615 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_615 := by
  arith_products_prefix rule_arithmetic_615
  all_goals refine Eq.trans ?_ (arith_smax_square _)
  all_goals simp only [arith_smax_comm]

/-- `arithmetic.isle:616`: symbolic modular product identity. -/
theorem ok_rule_arithmetic_616 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_616 := by
  arith_products_prefix rule_arithmetic_616
  all_goals refine Eq.trans ?_ (arith_smax_square _)
  all_goals simp only [arith_smax_comm]

/-- `arithmetic.isle:617`: symbolic modular product identity. -/
theorem ok_rule_arithmetic_617 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_617 := by
  arith_products_prefix rule_arithmetic_617
  all_goals refine Eq.trans ?_ (arith_smax_square _)
  all_goals simp only [arith_smax_comm]

/-- `arithmetic.isle:618`: symbolic modular product identity. -/
theorem ok_rule_arithmetic_618 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_618 := by
  arith_products_prefix rule_arithmetic_618
  all_goals refine Eq.trans ?_ (arith_smax_square _)
  all_goals simp only [arith_smax_comm]

/-- `arithmetic.isle:619`: symbolic modular product identity. -/
theorem ok_rule_arithmetic_619 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_619 := by
  arith_products_prefix rule_arithmetic_619
  all_goals refine Eq.trans ?_ (arith_umax_square _)
  all_goals simp only [arith_umax_comm]

/-- `arithmetic.isle:620`: symbolic modular product identity. -/
theorem ok_rule_arithmetic_620 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_620 := by
  arith_products_prefix rule_arithmetic_620
  all_goals refine Eq.trans ?_ (arith_umax_square _)
  all_goals simp only [arith_umax_comm]

/-- `arithmetic.isle:621`: symbolic modular product identity. -/
theorem ok_rule_arithmetic_621 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_621 := by
  arith_products_prefix rule_arithmetic_621
  all_goals refine Eq.trans ?_ (arith_umax_square _)
  all_goals simp only [arith_umax_comm]

/-- `arithmetic.isle:622`: symbolic modular product identity. -/
theorem ok_rule_arithmetic_622 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_622 := by
  arith_products_prefix rule_arithmetic_622
  all_goals refine Eq.trans ?_ (arith_umax_square _)
  all_goals simp only [arith_umax_comm]

-- Concrete non-vacuity witnesses for all four width-parametric helpers.
example : Sem.smax (128#8) (127#8) = Sem.smax (127#8) (128#8) := arith_smax_comm _ _
example : Sem.umax (32768#16) (32767#16) = Sem.umax (32767#16) (32768#16) := arith_umax_comm _ _
example : Sem.smax (-(128#8)) (128#8) * Sem.smax (-(128#8)) (128#8) = (128#8) * (128#8) :=
  arith_smax_square _
example : Sem.umax (-(255#8)) (255#8) * Sem.umax (-(255#8)) (255#8) = (255#8) * (255#8) :=
  arith_umax_square _

-- Both inner-negation positions, with high-bit and overflowing products.
example :
    Sem.ineg (Sem.imul (Sem.ineg (3#128)) (0x80000000000000000000000000000000#128)) =
      Sem.imul (0x80000000000000000000000000000000#128) (3#128) ∧
    Sem.ineg (Sem.imul (Sem.ineg (0xffffffffffffffffffffffffffffffff#128)) (7#128)) =
      Sem.imul (7#128) (0xffffffffffffffffffffffffffffffff#128) := by decide
example :
    Sem.ineg (Sem.imul (0x8000000000000000#64) (Sem.ineg (3#64))) =
      Sem.imul (0x8000000000000000#64) (3#64) ∧
    Sem.ineg (Sem.imul (7#64) (Sem.ineg (0xffffffffffffffff#64))) =
      Sem.imul (7#64) (0xffffffffffffffff#64) := by decide

-- Root 615: both ordering branches and the signed-minimum tie.
example :
    Sem.imul (Sem.smax (Sem.ineg (1#8)) (1#8)) (Sem.smax (Sem.ineg (1#8)) (1#8)) = 1#8 ∧
    Sem.imul (Sem.smax (Sem.ineg (255#8)) (255#8)) (Sem.smax (Sem.ineg (255#8)) (255#8)) = 1#8 ∧
    Sem.imul (Sem.smax (Sem.ineg (128#8)) (128#8)) (Sem.smax (Sem.ineg (128#8)) (128#8)) = 0#8 := by decide

-- Root 616: both ordering branches and the signed-minimum tie.
example :
    Sem.imul (Sem.smax (Sem.ineg (1#16)) (1#16)) (Sem.smax (1#16) (Sem.ineg (1#16))) = 1#16 ∧
    Sem.imul (Sem.smax (Sem.ineg (65535#16)) (65535#16)) (Sem.smax (65535#16) (Sem.ineg (65535#16))) = 1#16 ∧
    Sem.imul (Sem.smax (Sem.ineg (32768#16)) (32768#16)) (Sem.smax (32768#16) (Sem.ineg (32768#16))) = 0#16 := by decide

-- Root 617: both ordering branches and the signed-minimum tie.
example :
    Sem.imul (Sem.smax (1#64) (Sem.ineg (1#64))) (Sem.smax (Sem.ineg (1#64)) (1#64)) = 1#64 ∧
    Sem.imul (Sem.smax (18446744073709551615#64) (Sem.ineg (18446744073709551615#64))) (Sem.smax (Sem.ineg (18446744073709551615#64)) (18446744073709551615#64)) = 1#64 ∧
    Sem.imul (Sem.smax (9223372036854775808#64) (Sem.ineg (9223372036854775808#64))) (Sem.smax (Sem.ineg (9223372036854775808#64)) (9223372036854775808#64)) = 0#64 := by decide

-- Root 618: both ordering branches and the signed-minimum tie.
example :
    Sem.imul (Sem.smax (1#128) (Sem.ineg (1#128))) (Sem.smax (1#128) (Sem.ineg (1#128))) = 1#128 ∧
    Sem.imul (Sem.smax (340282366920938463463374607431768211455#128) (Sem.ineg (340282366920938463463374607431768211455#128))) (Sem.smax (340282366920938463463374607431768211455#128) (Sem.ineg (340282366920938463463374607431768211455#128))) = 1#128 ∧
    Sem.imul (Sem.smax (170141183460469231731687303715884105728#128) (Sem.ineg (170141183460469231731687303715884105728#128))) (Sem.smax (170141183460469231731687303715884105728#128) (Sem.ineg (170141183460469231731687303715884105728#128))) = 0#128 := by decide

-- Root 619: both ordering branches and the signed-minimum tie.
example :
    Sem.imul (Sem.umax (Sem.ineg (1#8)) (1#8)) (Sem.umax (Sem.ineg (1#8)) (1#8)) = 1#8 ∧
    Sem.imul (Sem.umax (Sem.ineg (255#8)) (255#8)) (Sem.umax (Sem.ineg (255#8)) (255#8)) = 1#8 ∧
    Sem.imul (Sem.umax (Sem.ineg (128#8)) (128#8)) (Sem.umax (Sem.ineg (128#8)) (128#8)) = 0#8 := by decide

-- Root 620: both ordering branches and the signed-minimum tie.
example :
    Sem.imul (Sem.umax (Sem.ineg (1#16)) (1#16)) (Sem.umax (1#16) (Sem.ineg (1#16))) = 1#16 ∧
    Sem.imul (Sem.umax (Sem.ineg (65535#16)) (65535#16)) (Sem.umax (65535#16) (Sem.ineg (65535#16))) = 1#16 ∧
    Sem.imul (Sem.umax (Sem.ineg (32768#16)) (32768#16)) (Sem.umax (32768#16) (Sem.ineg (32768#16))) = 0#16 := by decide

-- Root 621: both ordering branches and the signed-minimum tie.
example :
    Sem.imul (Sem.umax (1#64) (Sem.ineg (1#64))) (Sem.umax (Sem.ineg (1#64)) (1#64)) = 1#64 ∧
    Sem.imul (Sem.umax (18446744073709551615#64) (Sem.ineg (18446744073709551615#64))) (Sem.umax (Sem.ineg (18446744073709551615#64)) (18446744073709551615#64)) = 1#64 ∧
    Sem.imul (Sem.umax (9223372036854775808#64) (Sem.ineg (9223372036854775808#64))) (Sem.umax (Sem.ineg (9223372036854775808#64)) (9223372036854775808#64)) = 0#64 := by decide

-- Root 622: both ordering branches and the signed-minimum tie.
example :
    Sem.imul (Sem.umax (1#128) (Sem.ineg (1#128))) (Sem.umax (1#128) (Sem.ineg (1#128))) = 1#128 ∧
    Sem.imul (Sem.umax (340282366920938463463374607431768211455#128) (Sem.ineg (340282366920938463463374607431768211455#128))) (Sem.umax (340282366920938463463374607431768211455#128) (Sem.ineg (340282366920938463463374607431768211455#128))) = 1#128 ∧
    Sem.imul (Sem.umax (170141183460469231731687303715884105728#128) (Sem.ineg (170141183460469231731687303715884105728#128))) (Sem.umax (170141183460469231731687303715884105728#128) (Sem.ineg (170141183460469231731687303715884105728#128))) = 0#128 := by decide

end Opt.Proof
