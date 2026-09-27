/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license.

# Tactics used by the generated proofs
-/
import FV.Validate.Rules
import FV.Validate.Frame
import FV.Validate.StepThms

namespace Validate

/-- Side conditions of a step theorem (program, PC, error, SP alignment) for the current Arm
state, from the given hypotheses about the segment's start state. -/
syntax "vside" "[" Lean.Parser.Tactic.simpArg,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| vside [$hs,*]) =>
    `(tactic| simp (config := {decide := true}) only [state_simp_rules, vsimp, List.length_cons, List.length_nil, RegsHold_cons, RegsHold_nil, and_true, $hs,*])

/-- Evaluate the pending CLIF computation (operand lookups, `evalInst`, `enterBlock`, type
checks, register-file updates) with the given register-file hypotheses. -/
syntax "vclif" "[" Lean.Parser.Tactic.simpArg,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| vclif [$hs,*]) =>
    `(tactic| simp (config := {decide := true}) only [Clif.evalInst, Clif.Frame.getAs,
      Clif.Frame.get, Clif.Frame.getMany, Clif.Val.as?_mk, Clif.Res.ofOption_some,
      Clif.Res.ofOption_none, Clif.Res.check_true, Clif.Res.check_false, Clif.checkTys,
      Clif.Res.check, ResK_bind, ResK_ok, ResK_pure, ResK_stuck, ResK_trap,
      Clif.Regs.setMany_cons, Clif.Regs.setMany_nil, Clif.Regs.set, Option.elim,
      Clif.enterBlock, Clif.Sem.div, Clif.Sem.udiv, Clif.Sem.sdiv, Clif.Sem.urem, Clif.Sem.srem,
      Clif.Res.ofExcept_ok, Clif.Res.ofExcept_error, ofExcept_ite, ResK_ite, Clif.LoadOp.size, Clif.StoreOp.size,
      List.map, ↓reduceIte, true_implies, not_true_eq_false, false_implies, and_true,
      true_and, as?_i8, as?_i16, as?_i32, as?_i64, as?_i128, $hs,*])

/-- Close a relation fact about the current state: by rewriting with the given hypotheses, or
by bit-blasting after rewriting. -/
syntax "vfact" "[" Lean.Parser.Tactic.simpArg,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| vfact [$hs,*]) =>
    `(tactic| first
      | (simp (config := {decide := true}) only [state_simp_rules, vsimp, List.length_cons,
          List.length_nil, RegsHold_cons, RegsHold_nil, and_true, $hs,*]; done)
      | (simp (config := {decide := true, failIfUnchanged := false}) only [state_simp_rules,
          vsimp, vsem, RegsHold_cons, RegsHold_nil, and_true, true_and, $hs,*]; bv_decide))

/-- `urem` as Cranelift lowers it (`udiv` then `msub`). -/
@[vsem] theorem sub_udiv_mul {w : Nat} (x y : BitVec w) : x - x / y * y = x % y := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have h1 : x.toNat / y.toNat * y.toNat ≤ x.toNat := Nat.div_mul_le_self _ _
  have h2 : (x / y * y).toNat = x.toNat / y.toNat * y.toNat := by
    rw [BitVec.toNat_mul, BitVec.toNat_udiv]; exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h2]; exact h1), h2, BitVec.toNat_umod]
  have := Nat.mod_add_div x.toNat y.toNat
  rw [Nat.mul_comm] at this
  omega

@[vsem] theorem ite_true_eq_cond {α : Sort _} (b : Bool) [h : Decidable (b = true)] (x y : α) :
    @ite α (b = true) h x y = (bif b then x else y) := by cases b <;> simp

@[vsem] theorem bool8_eq_cond (b : Bool) : Clif.Sem.bool8 b = (bif b then 1#8 else 0#8) := by
  cases b <;> rfl

attribute [vsem] Clif.Sem.truthy Clif.Sem.icmp Clif.Sem.intcc Clif.Sem.binary
  Clif.Sem.iadd Clif.Sem.isub Clif.Sem.imul Clif.Sem.band Clif.Sem.bor Clif.Sem.bxor
  Clif.Sem.bnot Clif.Sem.ineg Clif.Sem.unary Clif.Sem.uextend Clif.Sem.sextend
  Clif.Sem.ireduce Clif.Sem.umulhi Clif.Sem.smulhi Clif.Sem.shift Clif.Sem.shiftAmt
  Clif.Sem.ishl Clif.Sem.ushr Clif.Sem.sshr Clif.Sem.rotl Clif.Sem.rotr

end Validate
