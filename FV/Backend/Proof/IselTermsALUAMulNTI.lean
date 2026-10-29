module

public import FV.Backend.Proof.IselTermsALUAMulN
public import FV.Backend.Proof.IselBaseTI

@[expose] public section

/-!
# `IselTermsALUAMulN` over typed contexts (S11e5 Stage C, slice 7)

`put_in_reg_sext64`/`put_in_reg_zext64` contracts over `CtxInvT`, the value in an integer
position.
-/

namespace Backend.Proof
open Isle Isle.Interp Isle.Aarch64
section Extern
variable (ctx : Ctx) (st : LState)
end Extern
variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)
section Helpers
variable (st : LState) (tr : Array RuleId) (n : Nat)
end Helpers
section Ext64
variable (st : LState) (tr : Array RuleId) (n : Nat)
end Ext64

section Contract
variable {f : Clif.Function} (hctx : CtxInvT f ctx) (st : LState) (tr : Array RuleId) (n : Nat)

include hp hc hctx in
/-- **`put_in_reg_sext64 x` returned `a`**: `x` has a type `t`; if `t` has at most 32 bits, `a`
is a fresh vreg written by `sxt` from `t.bits` to 64 bits, if `t = I64`, `a` is `x`'s register. -/
theorem sext64_invTI {x : Nat} {a : V} {st2 : LState} {tr2 : Array RuleId}
    (h : (applyTerm p (sem ctx) cfg (n+60) 27 557 [.value x]).run (st, tr) = .ok (some a, (st2, tr2)))
    (hxI : IntPos ctx x := by int_posA) :
    ∃ t, ctx.valueType? x = some t ∧ ctx.valueReg? x = some (.vreg x .int) ∧
      ((t.bits ≤ 32 ∧ a = .reg (st.fresh .int).1 ∧
          st2 = (st.fresh .int).2.emit (.extend (st.fresh .int).1 (.vreg x .int) true t.bits 64)) ∨
        (t = .int 64 ∧ a = .reg (.vreg x .int) ∧ st2 = st)) := by
  cases hvt : ctx.valueType? x with
  | none => exact absurd h (sext64_run_novt hp ctx st tr n hvt _ _)
  | some t =>
  have hx := hctx.typedRegI x t hvt
  refine ⟨t, rfl, hx, ?_⟩
  by_cases h32 : t.bits ≤ 32
  · obtain ⟨tr', he⟩ := sext64_run_narrow hp ctx hc st tr n hvt h32 hx
    rw [he] at h
    simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact .inl ⟨h32, rfl, rfl⟩
  · by_cases h64 : t = .int 64
    · subst h64
      obtain ⟨tr', he⟩ := sext64_run_64 hp ctx hc st tr n hvt hx
      rw [he] at h
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact .inr ⟨rfl, rfl, rfl⟩
    · exact absurd h (sext64_run_other hp ctx hc st tr n hvt h32 h64 _ _)

include hp hc hctx in
theorem zext64_invTI {x : Nat} {a : V} {st2 : LState} {tr2 : Array RuleId}
    (h : (applyTerm p (sem ctx) cfg (n+60) 27 558 [.value x]).run (st, tr) = .ok (some a, (st2, tr2)))
    (hxI : IntPos ctx x := by int_posA) :
    ∃ t, ctx.valueType? x = some t ∧ ctx.valueReg? x = some (.vreg x .int) ∧
      ((t.bits ≤ 32 ∧ a = .reg (st.fresh .int).1 ∧
          st2 = (st.fresh .int).2.emit (.extend (st.fresh .int).1 (.vreg x .int) false t.bits 64)) ∨
        (t = .int 64 ∧ a = .reg (.vreg x .int) ∧ st2 = st)) := by
  cases hvt : ctx.valueType? x with
  | none => exact absurd h (zext64_run_novt hp ctx st tr n hvt _ _)
  | some t =>
  have hx := hctx.typedRegI x t hvt
  refine ⟨t, rfl, hx, ?_⟩
  by_cases h32 : t.bits ≤ 32
  · obtain ⟨tr', he⟩ := zext64_run_narrow hp ctx hc st tr n hvt h32 hx
    rw [he] at h
    simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact .inl ⟨h32, rfl, rfl⟩
  · by_cases h64 : t = .int 64
    · subst h64
      obtain ⟨tr', he⟩ := zext64_run_64 hp ctx hc st tr n hvt hx
      rw [he] at h
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact .inr ⟨rfl, rfl, rfl⟩
    · exact absurd h (zext64_run_other hp ctx hc st tr n hvt h32 h64 _ _)

end Contract

end Backend.Proof
