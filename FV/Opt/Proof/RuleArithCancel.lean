import FV.Opt.Proof.RuleInfraIcmp
import FV.Opt.Proof.RuleRestEmbedSshr
import FV.Opt.Proof.RuleRestEmbedRotl
import FV.Opt.Proof.RuleRestEmbedRotr
import FV.Opt.Proof.RuleIntSplit
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace Opt.Proof
open Isle Isle.Opt Clif
attribute [local implicit_reducible] Ty.width
set_option hygiene false in
local macro "arith_cancel_rule " r:ident : tactic => `(tactic| (
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
  all_goals apply val_congr
  all_goals fin_bits_k))

/-- `arithmetic.isle:410`: repeated-operand comparison cancellation. -/
theorem ok_rule_arithmetic_410 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_410 := by
  arith_cancel_rule rule_arithmetic_410

/-- `arithmetic.isle:411`: repeated-operand comparison cancellation. -/
theorem ok_rule_arithmetic_411 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_411 := by
  arith_cancel_rule rule_arithmetic_411

/-- `arithmetic.isle:414`: repeated-operand comparison cancellation. -/
theorem ok_rule_arithmetic_414 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_414 := by
  arith_cancel_rule rule_arithmetic_414

/-- `arithmetic.isle:415`: repeated-operand comparison cancellation. -/
theorem ok_rule_arithmetic_415 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_415 := by
  arith_cancel_rule rule_arithmetic_415

/-- `arithmetic.isle:418`: repeated-operand comparison cancellation. -/
theorem ok_rule_arithmetic_418 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_418 := by
  arith_cancel_rule rule_arithmetic_418

/-- `arithmetic.isle:419`: repeated-operand comparison cancellation. -/
theorem ok_rule_arithmetic_419 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_419 := by
  arith_cancel_rule rule_arithmetic_419

/-- `arithmetic.isle:420`: repeated-operand comparison cancellation. -/
theorem ok_rule_arithmetic_420 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_420 := by
  arith_cancel_rule rule_arithmetic_420

/-- `arithmetic.isle:421`: repeated-operand comparison cancellation. -/
theorem ok_rule_arithmetic_421 {p : Isle.Program} (hd : Data p) : RuleOk p rule_arithmetic_421 := by
  arith_cancel_rule rule_arithmetic_421

-- Root 410: both outcomes, including wrapping arithmetic.
example :
    Sem.icmp .ne (Sem.binary .isub (128#8) (0#8)) (128#8) = 0#8 ∧
    Sem.icmp .ne (Sem.binary .isub (128#8) (1#8)) (128#8) = 1#8 := by decide

-- Root 411: both outcomes, including wrapping arithmetic.
example :
    Sem.icmp .ne (32768#16) (Sem.binary .isub (32768#16) (0#16)) = 0#8 ∧
    Sem.icmp .ne (32768#16) (Sem.binary .isub (32768#16) (1#16)) = 1#8 := by decide

-- Root 414: both outcomes, including wrapping arithmetic.
example :
    Sem.icmp .eq (Sem.binary .isub (2147483648#32) (0#32)) (2147483648#32) = 1#8 ∧
    Sem.icmp .eq (Sem.binary .isub (2147483648#32) (1#32)) (2147483648#32) = 0#8 := by decide

-- Root 415: both outcomes, including wrapping arithmetic.
example :
    Sem.uextend 128 (0#64) = 0#128 ∧
    Sem.icmp .eq (170141183460469231731687303715884105728#128) (Sem.binary .isub (170141183460469231731687303715884105728#128) (0#128)) = 1#8 ∧
    Sem.icmp .eq (170141183460469231731687303715884105728#128) (Sem.binary .isub (170141183460469231731687303715884105728#128) (1#128)) = 0#8 := by decide

-- Root 418: both outcomes, including wrapping arithmetic.
example :
    Sem.icmp .eq (Sem.binary .iadd (0#8) (255#8)) (255#8) = 1#8 ∧
    Sem.icmp .eq (Sem.binary .iadd (1#8) (255#8)) (255#8) = 0#8 := by decide

-- Root 419: both outcomes, including wrapping arithmetic.
example :
    Sem.icmp .eq (Sem.binary .iadd (65535#16) (0#16)) (65535#16) = 1#8 ∧
    Sem.icmp .eq (Sem.binary .iadd (65535#16) (1#16)) (65535#16) = 0#8 := by decide

-- Root 420: both outcomes, including wrapping arithmetic.
example :
    Sem.icmp .eq (18446744073709551615#64) (Sem.binary .iadd (0#64) (18446744073709551615#64)) = 1#8 ∧
    Sem.icmp .eq (18446744073709551615#64) (Sem.binary .iadd (1#64) (18446744073709551615#64)) = 0#8 := by decide

-- Root 421: both outcomes, including wrapping arithmetic.
example :
    Sem.uextend 128 (0#64) = 0#128 ∧
    Sem.icmp .eq (340282366920938463463374607431768211455#128) (Sem.binary .iadd (340282366920938463463374607431768211455#128) (0#128)) = 1#8 ∧
    Sem.icmp .eq (340282366920938463463374607431768211455#128) (Sem.binary .iadd (340282366920938463463374607431768211455#128) (1#128)) = 0#8 := by decide

end Opt.Proof
