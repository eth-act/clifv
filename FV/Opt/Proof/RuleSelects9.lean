import FV.Opt.Proof.RuleInfraIcmp
import FV.Opt.Proof.RuleRestEmbedSshr
import FV.Opt.Proof.RuleRestEmbedRotl
import FV.Opt.Proof.RuleRestEmbedRotr
import FV.Opt.Proof.RuleInfraConst
import FV.Opt.Proof.RuleIntSplit

/-!
# `opts/selects.isle` (part 9): boolean results and redundant OR operands

Keep comparisons symbolic: their i8 result is either zero or one. Preserve unsigned
literal-match facts until the RHS has been evaluated, then normalize the literals and
apply width-independent select identities before the graph finisher.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt Clif

attribute [local implicit_reducible] Ty.width

/-- Selecting one or zero from an `icmp` is its zero extension. -/
theorem selects_icmp_one_zero (outWidth : Nat) (cc : IntCC) {w : Nat} (x y : BitVec w) :
    Sem.select (Sem.icmp cc x y) (1#outWidth) (0#outWidth) =
      Sem.uextend outWidth (Sem.icmp cc x y) := by
  unfold Sem.icmp
  generalize Sem.intcc cc x y = b
  cases b
  · change (0#outWidth) = (0#8).setWidth outWidth
    exact (BitVec.setWidth_zero outWidth 8).symm
  · change (1#outWidth) = (1#8).setWidth outWidth
    exact (BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by decide)).symm

/-- The equal-width arm of `uextend_maybe` returns the comparison itself. -/
theorem selects_icmp_one_zero_i8 (cc : IntCC) {w : Nat} (x y : BitVec w) :
    Sem.select (Sem.icmp cc x y) (1#8) (0#8) = Sem.icmp cc x y := by
  unfold Sem.icmp
  generalize Sem.intcc cc x y = b
  cases b <;> rfl

/-- In the false arm the condition is zero, so OR-ing it into the value is redundant. -/
theorem selects_or_one_left {w : Nat} (x y : BitVec w) :
    Sem.select x (1#w) (x ||| y) = Sem.select x (1#w) y := by
  by_cases h : x = 0#w <;> simp [Sem.select, Sem.truthy, h]

theorem selects_or_one_right {w : Nat} (x y : BitVec w) :
    Sem.select x (1#w) (y ||| x) = Sem.select x (1#w) y := by
  by_cases h : x = 0#w <;> simp [Sem.select, Sem.truthy, h]

-- Both comparison outcomes, the same-width arm and a widening arm are inhabited.
example : Sem.select (Sem.icmp .slt (0x80#8) 0) (1#64) 0 = 1 ∧
    Sem.uextend 64 (Sem.icmp .slt (0x80#8) 0) = 1 := by decide
example : Sem.select (Sem.icmp .eq (4#32) 5) (1#8) 0 = 0 ∧
    Sem.icmp .eq (4#32) 5 = 0 := by decide
example : Sem.select (Sem.icmp .eq (4#32) 4) (1#8) 0 = 1 ∧
    Sem.icmp .eq (4#32) 4 = 1 := by decide
example : Sem.select (0#8) (1#8) (0 ||| 0x80) = 0x80 ∧
    Sem.select (0#8) (1#8) (0x80 ||| 0) = 0x80 := by decide
example : Sem.select (0x8000000000000000#64) (1#64) (0x8000000000000000 ||| 7) = 1 ∧
    Sem.select (0x8000000000000000#64) (1#64) (7 ||| 0x8000000000000000) = 1 := by decide

macro "selects_one_literals" : tactic => `(tactic| (
  try simp (disch := assumption) only [asU64_imm64OfBits, ← Int.cast_ofNat_Int,
    Int.natCast_inj, toNat_eq_iff_ofNat, ofInt_imm64OfBits] at *
  opt_destruct
  all_goals subst_vars
  all_goals try simp only [Sem.binary, Sem.bor, BitVec.ofNat_eq_ofNat,
    BitVec.natCast_eq_ofNat, selects_icmp_one_zero_i8, selects_icmp_one_zero,
    selects_or_one_left, selects_or_one_right]))

set_option hygiene false in
macro "selects_one_rule " r:ident : tactic => `(tactic| (
  rule_intro $r
  rule_no_iflets
  rule_lhs_g hG
  all_goals try opt_den_subst
  all_goals opt_split_i128
  all_goals opt_split_int
  all_goals rule_rhs_y [tyInt_ofClif_notInt]
  all_goals opt_some_subst
  all_goals try opt_den_subst
  all_goals try opt_val_ty_subst
  all_goals selects_one_literals
  all_goals rule_finish_tv))

open Lean Elab Tactic in
elab "selects_one_noinfo " t:tacticSeq : tactic => withEnableInfoTree false (evalTactic t)

set_option maxHeartbeats 4000000 in
/-- `selects.isle:15`: select between one and zero using a comparison result. -/
theorem ok_rule_selects_15 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_15 := by
  selects_one_noinfo
    selects_one_rule rule_selects_15

set_option maxHeartbeats 4000000 in
/-- `selects.isle:188`: remove the condition from the false arm's OR. -/
theorem ok_rule_selects_188 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_188 := by
  selects_one_noinfo
    selects_one_rule rule_selects_188

set_option maxHeartbeats 4000000 in
/-- `selects.isle:189`: the reversed OR operands. -/
theorem ok_rule_selects_189 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_189 := by
  selects_one_noinfo
    selects_one_rule rule_selects_189

end Opt.Proof
