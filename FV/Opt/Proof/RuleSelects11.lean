import FV.Opt.Proof.RuleInfraIcmp

/-!
# `opts/selects.isle` (part 11): eliminate a conditional subtraction

The two `iconst_u ty n` patterns need not name the same graph class. Their
unsigned immediate matches nevertheless force equal bits at the common type.
Keep those matching facts until both sides have been evaluated, then identify
the constants and use the width-independent conditional identity.
-/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000
set_option Elab.async false

namespace Opt.Proof

open Isle Isle.Opt Clif

attribute [local implicit_reducible] Ty.width

/-- Equality permits substituting the constant only in the branch where it is
compared equal; inequality and reversed operands give the same identity. -/
theorem selects_sub_same_const {w : Nat} (x y n : BitVec w) :
    Sem.select (Sem.icmp .eq x n) (y - n) (y - x) = y - x ∧
    Sem.select (Sem.icmp .ne x n) (y - x) (y - n) = y - x ∧
    Sem.select (Sem.icmp .eq n x) (y - n) (y - x) = y - x ∧
    Sem.select (Sem.icmp .ne n x) (y - x) (y - n) = y - x := by
  by_cases h : x = n
  · subst x
    simp [Sem.select, Sem.icmp, Sem.intcc, Sem.bool8, Sem.truthy, bne]
  · simp [Sem.select, Sem.icmp, Sem.intcc, Sem.bool8, Sem.truthy, bne, h, Ne.symm h]

open Lean Elab Tactic in
elab "selects_sub_noinfo " t:tacticSeq : tactic => withEnableInfoTree false (evalTactic t)

macro "selects_sub_identity" : tactic => `(tactic| first
  | exact (selects_sub_same_const _ _ _).1
  | exact (selects_sub_same_const _ _ _).2.1
  | exact (selects_sub_same_const _ _ _).2.2.1
  | exact (selects_sub_same_const _ _ _).2.2.2)

macro "selects_sub_finish" : tactic => `(tactic| (
  -- Normalize only after graph matching and RHS evaluation: earlier rewriting
  -- would change the literal AST in the remaining matcher hypotheses.
  try simp (disch := assumption) only [asU64_imm64OfBits,
    ← Int.cast_ofNat_Int, Int.natCast_inj, BitVec.toNat_inj] at *
  opt_destruct
  all_goals subst_vars
  all_goals simp only [Sem.binary, Sem.isub]
  all_goals first | selects_sub_identity | (symm; selects_sub_identity)))

set_option maxHeartbeats 16000000 in
/-- `selects.isle:193`: equality with the constant on the right. -/
theorem ok_rule_selects_193 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_193 := by
  selects_sub_noinfo
    rule_pre_k rule_selects_193
    all_goals selects_sub_finish

set_option maxHeartbeats 16000000 in
/-- `selects.isle:194`: inequality and exchanged select arms. -/
theorem ok_rule_selects_194 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_194 := by
  selects_sub_noinfo
    rule_pre_k rule_selects_194
    all_goals selects_sub_finish

set_option maxHeartbeats 16000000 in
/-- `selects.isle:195`: equality with the constant on the left. -/
theorem ok_rule_selects_195 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_195 := by
  selects_sub_noinfo
    rule_pre_k rule_selects_195
    all_goals selects_sub_finish

set_option maxHeartbeats 16000000 in
/-- `selects.isle:196`: reversed inequality and exchanged select arms. -/
theorem ok_rule_selects_196 {p : Isle.Program} (hd : Data p) : RuleOk p rule_selects_196 := by
  selects_sub_noinfo
    rule_pre_k rule_selects_196
    all_goals selects_sub_finish

/-! Concrete unsigned-literal matches and evaluations. Each rule has both an
 equal and an unequal comparison; the evaluations include zero, the high bit,
 and modular subtraction wrapping below zero. -/

example : Ty.i8 ≠ .i128 ∧ Rust.asU64 (imm64OfBits (0#8)) = 0 ∧
    Rust.asU64 (imm64OfBits (0x80#8)) = 128 := by decide

example : Ty.i64 ≠ .i128 ∧
    Rust.asU64 (imm64OfBits (0x8000000000000000#64)) = 9223372036854775808 := by decide

-- An inhabited instance of all four width-independent helper conclusions.
example :
    Sem.select (Sem.icmp .eq (0x80#8) (0x80#8)) (0#8 - 0x80#8) (0#8 - 0x80#8) = 0#8 - 0x80#8 ∧
    Sem.select (Sem.icmp .ne (0x80#8) (0x80#8)) (0#8 - 0x80#8) (0#8 - 0x80#8) = 0#8 - 0x80#8 ∧
    Sem.select (Sem.icmp .eq (0x80#8) (0x80#8)) (0#8 - 0x80#8) (0#8 - 0x80#8) = 0#8 - 0x80#8 ∧
    Sem.select (Sem.icmp .ne (0x80#8) (0x80#8)) (0#8 - 0x80#8) (0#8 - 0x80#8) = 0#8 - 0x80#8 :=
  selects_sub_same_const (0x80#8) (0#8) (0x80#8)

-- 193: zero matches; unequal operands take the variable-subtraction arm.
example : Sem.icmp .eq (0#8) (0#8) = 1#8 ∧
    Sem.select (Sem.icmp .eq (0#8) (0#8)) (0#8 - 0#8) (0#8 - 0#8) = 0#8 ∧
    0#8 - 0#8 = 0#8 := by decide

example : Sem.icmp .eq (1#8) (0#8) = 0#8 ∧
    Sem.select (Sem.icmp .eq (1#8) (0#8)) (0#8 - 0#8) (0#8 - 1#8) = 255#8 ∧
    0#8 - 1#8 = 255#8 := by decide

-- 194: both outcomes, including the signed high bit as an unsigned immediate.
example : Sem.icmp .ne (0x8000#16) (0x8000#16) = 0#8 ∧
    Sem.select (Sem.icmp .ne (0x8000#16) (0x8000#16))
      (0#16 - 0x8000#16) (0#16 - 0x8000#16) = 0x8000#16 ∧
    0#16 - 0x8000#16 = 0x8000#16 := by decide

example : Sem.icmp .ne (5#8) (0#8) = 1#8 ∧
    Sem.select (Sem.icmp .ne (5#8) (0#8)) (2#8 - 5#8) (2#8 - 0#8) = 253#8 ∧
    2#8 - 5#8 = 253#8 := by decide

-- 195: the immediate is on the left of the equality.
example : Sem.icmp .eq (0x80000000#32) (0x80000000#32) = 1#8 ∧
    Sem.select (Sem.icmp .eq (0x80000000#32) (0x80000000#32))
      (1#32 - 0x80000000#32) (1#32 - 0x80000000#32) = 0x80000001#32 ∧
    1#32 - 0x80000000#32 = 0x80000001#32 := by decide

example : Sem.icmp .eq (0#16) (1#16) = 0#8 ∧
    Sem.select (Sem.icmp .eq (0#16) (1#16)) (0#16 - 0#16) (0#16 - 1#16) = 65535#16 ∧
    0#16 - 1#16 = 65535#16 := by decide

-- 196: the immediate is on the left of the inequality.
example : Sem.icmp .ne (0#64) (0#64) = 0#8 ∧
    Sem.select (Sem.icmp .ne (0#64) (0#64)) (0#64 - 0#64) (0#64 - 0#64) = 0#64 ∧
    0#64 - 0#64 = 0#64 := by decide

example : Sem.icmp .ne (0#64) (0x8000000000000000#64) = 1#8 ∧
    Sem.select (Sem.icmp .ne (0#64) (0x8000000000000000#64))
      (1#64 - 0x8000000000000000#64) (1#64 - 0#64) = 0x8000000000000001#64 ∧
    1#64 - 0x8000000000000000#64 = 0x8000000000000001#64 := by decide

end Opt.Proof
