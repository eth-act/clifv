import FV.Opt.Proof.RuleInfraIcmp
import FV.Opt.Proof.RuleRestEmbedSshr
import FV.Opt.Proof.RuleRestEmbedRotl
import FV.Opt.Proof.RuleRestEmbedRotr
import FV.Opt.Proof.RuleInfraConst
import FV.Opt.Proof.RuleIntSplit

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt Clif

attribute [local implicit_reducible] Ty.width

-- The selected operands have width `w`; comparison results have width 8.
-- In particular, moving the select must not use the result type for its operands.
theorem selects_eq_199 {v w : Nat} (x : BitVec v) (z y k : BitVec w) :
    Sem.select x (Sem.icmp .eq z y) (Sem.icmp .eq k y) =
      Sem.icmp .eq y (Sem.select x z k) := by
  cases hx : Sem.truthy x <;>
    simp only [Sem.select, hx, Bool.false_eq_true, ite_false, ite_true]
  all_goals
    simp only [Sem.icmp, Sem.intcc]
    apply congrArg Sem.bool8
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq]
    exact eq_comm

theorem selects_eq_200 {v w : Nat} (x : BitVec v) (z y k : BitVec w) :
    Sem.select x (Sem.icmp .eq z y) (Sem.icmp .eq y k) =
      Sem.icmp .eq y (Sem.select x z k) := by
  cases hx : Sem.truthy x <;>
    simp only [Sem.select, hx, Bool.false_eq_true, ite_false, ite_true]
  all_goals
    simp only [Sem.icmp, Sem.intcc]
    apply congrArg Sem.bool8
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq]
    exact eq_comm

theorem selects_eq_201 {v w : Nat} (x : BitVec v) (z y k : BitVec w) :
    Sem.select x (Sem.icmp .eq y z) (Sem.icmp .eq k y) =
      Sem.icmp .eq y (Sem.select x z k) := by
  cases hx : Sem.truthy x <;>
    simp only [Sem.select, hx, Bool.false_eq_true, ite_false, ite_true]
  all_goals
    simp only [Sem.icmp, Sem.intcc]
    apply congrArg Sem.bool8
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq]
    exact eq_comm

theorem selects_eq_202 {v w : Nat} (x : BitVec v) (z y k : BitVec w) :
    Sem.select x (Sem.icmp .eq y z) (Sem.icmp .eq y k) =
      Sem.icmp .eq y (Sem.select x z k) := by
  cases hx : Sem.truthy x <;>
    simp only [Sem.select, hx, Bool.false_eq_true, ite_false, ite_true]

-- Typed constant constructors have an internal optional if-let. Resolve it
-- before continuing to the `typeOf` reads of the outer equality constructor. The
-- constants' type is split on `isInt` first (`RuleIntSplit.lean`): at a float type
-- `iconst_u` has no rule.
set_option hygiene false in
macro "selects_compare_rhs" : tactic => `(tactic| (
  opt_eval hev [tyInt_ofClif_notInt]
  repeat' ((first | opt_split_typeof hev | split at hev) <;>
    (try (rename_i hq; opt_split_ite hq <;>
      (try simp only [Option.some.injEq, reduceCtorEq, Bool.false_eq_true,
        ite_false, ↓reduceIte] at hq) <;> (try subst hq))) <;>
    try opt_eval hev [tyInt_ofClif_notInt])
  all_goals (try (simp only [reduceCtorEq] at hev; done))
  all_goals (try simp only [Option.map_eq_some_iff, Option.map_eq_none_iff] at *)
  all_goals opt_destruct
  all_goals subst_vars
  all_goals (
    simp only [Except.ok.injEq, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false,
      V.value.injEq, reduceCtorEq] at hm <;>
      subst hm)
  all_goals opt_types))

macro "selects_compare_identity" : tactic => `(tactic| first
  | exact selects_eq_199 _ _ _ _
  | exact selects_eq_200 _ _ _ _
  | exact selects_eq_201 _ _ _ _
  | exact selects_eq_202 _ _ _ _)

macro "selects_compare_finish" : tactic => `(tactic| (
  try simp (disch := assumption) only [ofInt_asI64_low, asU64_imm64OfBits,
    ofInt_imm64OfBits, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  first | selects_compare_identity | (symm; selects_compare_identity)))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
/-- `selects.isle:199`: both equalities have the common operand on the right. -/
theorem ok_rule_selects_199 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_199 := by
  rule_intro rule_selects_199
  rule_lhs_g hG
  all_goals rule_no_iflets
  all_goals opt_split_i128
  all_goals opt_split_int
  all_goals selects_compare_rhs
  all_goals opt_some_subst
  all_goals (try opt_den_subst)
  all_goals (apply GraphOk.make_val hG (by opt_P); opt_node)
  all_goals (apply val_congr; selects_compare_finish)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
/-- `selects.isle:200`: the constant equality has the common operand on the left. -/
theorem ok_rule_selects_200 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_200 := by
  rule_intro rule_selects_200
  rule_lhs_g hG
  all_goals rule_no_iflets
  all_goals opt_split_i128
  all_goals opt_split_int
  all_goals selects_compare_rhs
  all_goals opt_some_subst
  all_goals (try opt_den_subst)
  all_goals (apply GraphOk.make_val hG (by opt_P); opt_node)
  all_goals (apply val_congr; selects_compare_finish)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
/-- `selects.isle:201`: the variable equality has the common operand on the left. -/
theorem ok_rule_selects_201 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_201 := by
  rule_intro rule_selects_201
  rule_lhs_g hG
  all_goals rule_no_iflets
  all_goals opt_split_i128
  all_goals opt_split_int
  all_goals selects_compare_rhs
  all_goals opt_some_subst
  all_goals (try opt_den_subst)
  all_goals (apply GraphOk.make_val hG (by opt_P); opt_node)
  all_goals (apply val_congr; selects_compare_finish)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
/-- `selects.isle:202`: both equalities have the common operand on the left. -/
theorem ok_rule_selects_202 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_202 := by
  rule_intro rule_selects_202
  rule_lhs_g hG
  all_goals rule_no_iflets
  all_goals opt_split_i128
  all_goals opt_split_int
  all_goals selects_compare_rhs
  all_goals opt_some_subst
  all_goals (try opt_den_subst)
  all_goals (apply GraphOk.make_val hG (by opt_P); opt_node)
  all_goals (apply val_congr; selects_compare_finish)

-- Each operand-order variant is exercised with both branch choices and both
-- equality outcomes. The 64-bit constant has its high bit set, while the
-- condition is 16 bits and each comparison result is 8 bits.
theorem selects_compare_constant_witness : Ty.i64 ≠ .i128 ∧
    Rust.asU64 (imm64OfBits (0x8000000000000000#64)) = 0x8000000000000000 ∧
    BitVec.ofInt 64 (Rust.asI64 0x8000000000000000) = 0x8000000000000000#64 := by
  decide

theorem selects_199_witnesses :
    Sem.select (0x8000#16) (Sem.icmp .eq (7#64) 7)
      (Sem.icmp .eq (0x8000000000000000#64) 7) = 1#8 ∧
    Sem.select (0x8000#16) (Sem.icmp .eq (9#64) 7)
      (Sem.icmp .eq (0x8000000000000000#64) 7) = 0#8 ∧
    Sem.select (0#16) (Sem.icmp .eq (9#64) 0x8000000000000000)
      (Sem.icmp .eq (0x8000000000000000#64) 0x8000000000000000) = 1#8 ∧
    Sem.select (0#16) (Sem.icmp .eq (7#64) 7)
      (Sem.icmp .eq (0x8000000000000000#64) 7) = 0#8 := by decide

theorem selects_200_witnesses :
    Sem.select (0x8000#16) (Sem.icmp .eq (7#64) 7)
      (Sem.icmp .eq (7#64) 0x8000000000000000) = 1#8 ∧
    Sem.select (0x8000#16) (Sem.icmp .eq (9#64) 7)
      (Sem.icmp .eq (7#64) 0x8000000000000000) = 0#8 ∧
    Sem.select (0#16) (Sem.icmp .eq (9#64) 0x8000000000000000)
      (Sem.icmp .eq (0x8000000000000000#64) 0x8000000000000000) = 1#8 ∧
    Sem.select (0#16) (Sem.icmp .eq (7#64) 7)
      (Sem.icmp .eq (7#64) 0x8000000000000000) = 0#8 := by decide

theorem selects_201_witnesses :
    Sem.select (0x8000#16) (Sem.icmp .eq (7#64) 7)
      (Sem.icmp .eq (0x8000000000000000#64) 7) = 1#8 ∧
    Sem.select (0x8000#16) (Sem.icmp .eq (7#64) 9)
      (Sem.icmp .eq (0x8000000000000000#64) 7) = 0#8 ∧
    Sem.select (0#16) (Sem.icmp .eq (0x8000000000000000#64) 9)
      (Sem.icmp .eq (0x8000000000000000#64) 0x8000000000000000) = 1#8 ∧
    Sem.select (0#16) (Sem.icmp .eq (7#64) 7)
      (Sem.icmp .eq (0x8000000000000000#64) 7) = 0#8 := by decide

theorem selects_202_witnesses :
    Sem.select (0x8000#16) (Sem.icmp .eq (7#64) 7)
      (Sem.icmp .eq (7#64) 0x8000000000000000) = 1#8 ∧
    Sem.select (0x8000#16) (Sem.icmp .eq (7#64) 9)
      (Sem.icmp .eq (7#64) 0x8000000000000000) = 0#8 ∧
    Sem.select (0#16) (Sem.icmp .eq (0x8000000000000000#64) 9)
      (Sem.icmp .eq (0x8000000000000000#64) 0x8000000000000000) = 1#8 ∧
    Sem.select (0#16) (Sem.icmp .eq (7#64) 7)
      (Sem.icmp .eq (7#64) 0x8000000000000000) = 0#8 := by decide

theorem selects_compare_rhs_witnesses :
    Sem.icmp .eq (7#64) (Sem.select (0x8000#16) 7 0x8000000000000000) = 1#8 ∧
    Sem.icmp .eq (7#64) (Sem.select (0x8000#16) 9 0x8000000000000000) = 0#8 ∧
    Sem.icmp .eq (0x8000000000000000#64)
      (Sem.select (0#16) 9 0x8000000000000000) = 1#8 ∧
    Sem.icmp .eq (7#64) (Sem.select (0#16) 7 0x8000000000000000) = 0#8 := by decide

end Opt.Proof
