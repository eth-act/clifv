import FV.Backend.Proof.StockValues
import FV.Backend.Proof.IselInterp
namespace Backend.Stock.Proof.ScalarShift
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem regs_shape (ctx : Ctx) (st : State) (x : Nat) :
    Stock.externCtor ctx T.put_in_regs [.value x] st =
      match ctx.defInst? x with
      | some i => if st.sunk[i]! then .unmodeled s!"demand for sunk instruction {i}" else
          match ctx.valueReg? x with
          | some r => .ok (.regs [r], st.mark x)
          | none => .unmodeled s!"put_in_regs v{x}"
      | none => match ctx.valueReg? x with
        | some r => .ok (.regs [r], st.mark x)
        | none => .unmodeled s!"put_in_regs v{x}" := by
  have legacy : Backend.externCtor ctx T.put_in_regs [.value x] (st.mark x).base =
      match ctx.valueReg? x with
      | some r => .ok (.regs [r], (st.mark x).base)
      | none => .unmodeled s!"put_in_regs v{x}" := rfl
  have delegated : (match Backend.externCtor ctx T.put_in_regs [.value x] (st.mark x).base with
      | .ok (v, b) => ExtResult.ok (v, {st.mark x with base := b})
      | .fail => ExtResult.fail | .unmodeled e => ExtResult.unmodeled e) =
      (match ctx.valueReg? x with
      | some r => .ok (.regs [r], st.mark x)
      | none => .unmodeled s!"put_in_regs v{x}") := by
    rw [legacy]
    cases ctx.valueReg? x <;> rfl
  simp only [T.put_in_regs] at delegated
  cases hd : ctx.defInst? x <;>
    simp [Stock.externCtor, T.put_in_regs, TId.mark_value_used, hd] <;>
      first | exact delegated | (split <;> first | rfl | exact delegated)

/-- Successful actual scalar requests certify source safety, the register map,
output and complete marked state; no independently supplied safety premise. -/
theorem stock_shift_put_in_regs_iff (ctx : Ctx) (st : State) (x : Nat) (v : V) (next : State) :
    Stock.externCtor ctx T.put_in_regs [.value x] st = .ok (v, next) ↔
      DemandAllowed ctx st x ∧ ∃ r, ctx.valueReg? x = some r ∧ v = .regs [r] ∧ next = st.mark x := by
  constructor
  · intro run
    rw [regs_shape] at run
    cases hd : ctx.defInst? x with
    | none =>
      rw [hd] at run
      cases hm : ctx.valueReg? x with
      | none => rw [hm] at run; cases run
      | some r =>
        rw [hm] at run
        cases run
        refine ⟨?_, r, rfl, rfl, rfl⟩
        intro i impossible
        rw [hd] at impossible
        cases impossible
    | some i =>
      rw [hd] at run
      cases hs : st.sunk[i]! with
      | true => simp only [hs, ite_true] at run; cases run
      | false =>
        simp only [hs, Bool.false_eq_true, ite_false] at run
        cases hm : ctx.valueReg? x with
        | none => rw [hm] at run; cases run
        | some r =>
          rw [hm] at run
          cases run
          refine ⟨?_, r, rfl, rfl, rfl⟩
          intro j defined
          rw [hd] at defined
          have same := Option.some.inj defined
          subst j
          exact hs
  · rintro ⟨safe, r, mapped, rfl, rfl⟩
    exact stock_put_in_regs ctx st x r mapped safe


end Backend.Stock.Proof.ScalarShift
