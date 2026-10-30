import FV.Opt.Proof.RuleInfraIcmp
import FV.Opt.Proof.RuleRestEmbedSshr
import FV.Opt.Proof.RuleRestEmbedRotl
import FV.Opt.Proof.RuleRestEmbedRotr
import FV.Opt.Proof.RuleIntSplit

/-!
# Comparisons of a select between distinct constants

Normalize both matched constant encodings before using the select identity. The
condition's value is opened before RHS type splitting, so an arbitrary condition
width, including i128's widened-zero constructor, is preserved. The constants' type variable
is split on `isInt` (`RuleIntSplit.lean`): at a float type `iconst_u` has no rule.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace Opt.Proof
open Isle Isle.Opt Clif
attribute [local implicit_reducible] Ty.width

private theorem icmp_select_eq_left {w cw : Nat} (c : BitVec cw) (a b : BitVec w) (h : a ≠ b) :
    Sem.icmp .eq (Sem.select c a b) a = Sem.icmp .ne c (0#cw) := by
  by_cases hc : c = 0#cw <;>
    simp [Sem.icmp, Sem.intcc, Sem.select, Sem.truthy, Sem.bool8, hc, h, Ne.symm h]
private theorem icmp_select_eq_right {w cw : Nat} (c : BitVec cw) (a b : BitVec w) (h : a ≠ b) :
    Sem.icmp .eq (Sem.select c a b) b = Sem.icmp .eq c (0#cw) := by
  by_cases hc : c = 0#cw <;>
    simp [Sem.icmp, Sem.intcc, Sem.select, Sem.truthy, Sem.bool8, hc, h, Ne.symm h]
private theorem icmp_select_ne_left {w cw : Nat} (c : BitVec cw) (a b : BitVec w) (h : a ≠ b) :
    Sem.icmp .ne (Sem.select c a b) a = Sem.icmp .eq c (0#cw) := by
  by_cases hc : c = 0#cw <;>
    simp [Sem.icmp, Sem.intcc, Sem.select, Sem.truthy, Sem.bool8, hc, h, Ne.symm h]
private theorem icmp_select_ne_right {w cw : Nat} (c : BitVec cw) (a b : BitVec w) (h : a ≠ b) :
    Sem.icmp .ne (Sem.select c a b) b = Sem.icmp .ne c (0#cw) := by
  by_cases hc : c = 0#cw <;>
    simp [Sem.icmp, Sem.intcc, Sem.select, Sem.truthy, Sem.bool8, hc, h, Ne.symm h]

set_option hygiene false in
local macro "icmp_select_prefix " r:ident : tactic => `(tactic| (
  rule_intro $r
  rule_lhs_g hG
  all_goals rule_iflets_c []
  all_goals try opt_den_subst
  all_goals opt_cases_val
  all_goals (try simp only [Val.ty, Val.bits] at *; subst_vars)
  all_goals opt_split_i128
  all_goals opt_split_int
  all_goals rule_rhs_y [tyInt_ofClif_notInt]
  all_goals opt_some_subst
  all_goals try opt_den_subst
  all_goals (apply GraphOk.make_val hG (by opt_P); opt_node_x)
  all_goals apply val_congr
  all_goals simp (disch := assumption) only [asU64_imm64OfBits, Int.natCast_inj,
    BitVec.toNat_inj, beq_iff_eq, beq_eq_false_iff_ne] at *
  all_goals subst_vars
  all_goals simp only [Val.bits, Sem.uextend, BitVec.ofInt_ofNat, BitVec.setWidth_zero]))

/-- `icmp.isle:386`. -/
theorem ok_rule_icmp_386 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_386 := by
  icmp_select_prefix rule_icmp_386
  all_goals exact icmp_select_eq_left _ _ _ (by intro h; subst h; contradiction)

/-- `icmp.isle:394`. -/
theorem ok_rule_icmp_394 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_394 := by
  icmp_select_prefix rule_icmp_394
  all_goals exact icmp_select_eq_right _ _ _ (by intro h; subst h; contradiction)

/-- `icmp.isle:402`. -/
theorem ok_rule_icmp_402 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_402 := by
  icmp_select_prefix rule_icmp_402
  all_goals exact icmp_select_ne_left _ _ _ (by intro h; subst h; contradiction)

/-- `icmp.isle:410`. -/
theorem ok_rule_icmp_410 {p : Isle.Program} (hd : Data p) : RuleOk p rule_icmp_410 := by
  icmp_select_prefix rule_icmp_410
  all_goals exact icmp_select_ne_right _ _ _ (by intro h; subst h; contradiction)

-- The literal-distinctness guard and both condition outcomes are inhabited.
example : (1#8) ≠ 2#8 ∧
    Sem.icmp .eq (Sem.select (0#64) (1#8) (2#8)) (1#8) = 0#8 ∧
    Sem.icmp .eq (Sem.select (0x8000000000000000#64) (1#8) (2#8)) (1#8) = 1#8 := by decide
example : (255#8) ≠ 0#8 ∧
    Sem.icmp .eq (Sem.select (0#128) (255#8) (0#8)) (0#8) = 1#8 ∧
    Sem.icmp .eq (Sem.select (2#128) (255#8) (0#8)) (0#8) = 0#8 := by decide
example : (0#64) ≠ 0x8000000000000000#64 ∧
    Sem.icmp .ne (Sem.select (0#8) (0#64) (0x8000000000000000#64)) (0#64) = 1#8 ∧
    Sem.icmp .ne (Sem.select (128#8) (0#64) (0x8000000000000000#64)) (0#64) = 0#8 := by decide
example : (1#32) ≠ 2#32 ∧
    Sem.icmp .ne (Sem.select (0#16) (1#32) (2#32)) (2#32) = 0#8 ∧
    Sem.icmp .ne (Sem.select (65535#16) (1#32) (2#32)) (2#32) = 1#8 := by decide

end Opt.Proof
