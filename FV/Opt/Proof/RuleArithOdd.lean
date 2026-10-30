import FV.Opt.Proof.RuleInfraIcmp
import FV.Opt.Proof.RuleArithOddSem
import FV.Opt.Proof.RuleInfraPow2

/-!
# Odd-multiplier comparison cancellation

The generated `iconst_u` extractor has no `fits_in_64` guard, but the graph's
presentation does: `ofInst` never presents `iconst.i128`, and `toInst` rejects it.
Thus the matched constants themselves supply the non-i128 fact; no original
`RuleOk` premise or rule guard is changed here. The unsigned immediate quotient
is handled exactly, including i64 constants whose stored Imm64 is negative.
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option Elab.async false

namespace Opt.Proof

open Isle Isle.Opt Clif
attribute [local implicit_reducible] Ty.width

set_option hygiene false in
local macro "rule_odd " r:ident : tactic => `(tactic| (
  rule_intro $r
  rule_lhs_g hG
  all_goals try simp (disch := assumption) only [asU64_imm64OfBits] at *
  all_goals rule_iflets_c [asU64_imm64OfBits]
  all_goals simp only [Int.reduceBEq, Bool.false_eq_true, ite_false, except_ok_bind',
    Option.map_some, toExt_ok_some, ExtResult.ok.injEq, Prod.mk.injEq] at *
  all_goals opt_destruct
  all_goals subst_vars
  all_goals simp only [V.beq_int, beq_iff_eq] at *
  all_goals have hodd_ne (x : Int) (hx : x % 2 = 1) : x ≠ 0 := by omega
  all_goals simp (disch := omega) only [hodd_ne, ite_false, Option.map_some,
    toExt_ok_some, ExtResult.ok.injEq, Prod.mk.injEq] at *
  all_goals opt_destruct
  all_goals subst_vars
  all_goals simp only [V.beq_int, beq_iff_eq] at *
  all_goals pow2_wfacts
  all_goals try opt_den_subst
  all_goals rule_rhs_y [Int.reduceBEq, beq_iff_eq, hodd_ne,
    Interp.matchAll.eq_1, Interp.matchAll.eq_2]
  all_goals opt_some_subst
  all_goals try opt_den_subst
  all_goals (apply GraphOk.make_val hG (by opt_P); opt_node_x)
  all_goals try decide
  all_goals apply val_congr
  all_goals simp only [Sem.binary, Sem.imul, Sem.icmp, Sem.intcc, bne]
  all_goals simp (disch := first | assumption | omega) only
    [odd_mul_quotient_beq, odd_mul_quotient_beq_left,
      odd_mul_quotient_beq_rev, odd_mul_quotient_beq_left_rev]))

/-- `arithmetic.isle:251`: constant on the left, odd multiplier on the right, `ne`. -/
theorem ok_rule_arithmetic_251 {p : Isle.Program} (hd : Data p) :
    RuleOk p rule_arithmetic_251 := by
  rule_odd rule_arithmetic_251

/-- `arithmetic.isle:256`: constant on the left, odd multiplier on the left, `ne`. -/
theorem ok_rule_arithmetic_256 {p : Isle.Program} (hd : Data p) :
    RuleOk p rule_arithmetic_256 := by
  rule_odd rule_arithmetic_256

/-- `arithmetic.isle:261`: constant on the right, odd multiplier on the right, `ne`. -/
theorem ok_rule_arithmetic_261 {p : Isle.Program} (hd : Data p) :
    RuleOk p rule_arithmetic_261 := by
  rule_odd rule_arithmetic_261

/-- `arithmetic.isle:266`: constant on the right, odd multiplier on the left, `ne`. -/
theorem ok_rule_arithmetic_266 {p : Isle.Program} (hd : Data p) :
    RuleOk p rule_arithmetic_266 := by
  rule_odd rule_arithmetic_266

/-- `arithmetic.isle:273`: constant on the left, odd multiplier on the right, `eq`. -/
theorem ok_rule_arithmetic_273 {p : Isle.Program} (hd : Data p) :
    RuleOk p rule_arithmetic_273 := by
  rule_odd rule_arithmetic_273

/-- `arithmetic.isle:278`: constant on the left, odd multiplier on the left, `eq`. -/
theorem ok_rule_arithmetic_278 {p : Isle.Program} (hd : Data p) :
    RuleOk p rule_arithmetic_278 := by
  rule_odd rule_arithmetic_278

/-- `arithmetic.isle:283`: constant on the right, odd multiplier on the right, `eq`. -/
theorem ok_rule_arithmetic_283 {p : Isle.Program} (hd : Data p) :
    RuleOk p rule_arithmetic_283 := by
  rule_odd rule_arithmetic_283

/-- `arithmetic.isle:288`: constant on the right, odd multiplier on the left, `eq`. -/
theorem ok_rule_arithmetic_288 {p : Isle.Program} (hd : Data p) :
    RuleOk p rule_arithmetic_288 := by
  rule_odd rule_arithmetic_288

-- A common joint-premise witness for all eight roots: i8 C=3, D=21.
-- Both operand orders match presented constants and both guards succeed.
-- y=7 and y=8 exercise both comparison outcomes for each condition code.
example : ofInst (.iconst .i8 (3#8)) ≠ none ∧
    ofInst (.iconst .i8 (21#8)) ≠ none ∧
    Rust.asU64 (imm64OfBits (21#8)) % Rust.asU64 (imm64OfBits (3#8)) = 0 ∧
    Rust.asU64 (imm64OfBits (3#8)) % 2 = 1 ∧
    Sem.icmp .eq (21#8) ((7#8) * (3#8)) = 1#8 ∧
    Sem.icmp .eq ((3#8) * (7#8)) (21#8) = 1#8 ∧
    Sem.icmp .ne (21#8) ((8#8) * (3#8)) = 1#8 ∧
    Sem.icmp .ne ((3#8) * (8#8)) (21#8) = 1#8 := by decide

end Opt.Proof
