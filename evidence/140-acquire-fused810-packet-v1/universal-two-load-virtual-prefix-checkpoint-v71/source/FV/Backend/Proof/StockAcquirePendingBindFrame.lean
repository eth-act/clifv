import FV.Backend.Proof.StockAcquirePendingMarksTrace

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

private def markFields (state : State) := (state.entryColor,state.color,state.sunk)

private theorem alias_mark_fields {before after : State} {dst src : Reg}
    (run : before.setAlias dst src = .ok after) : markFields after = markFields before := by
  cases dst <;> cases src <;>
    simp only [State.setAlias,bind,Except.bind,pure,Except.pure,
      throw,throwThe,MonadExceptOf.throw] at run
  all_goals repeat' first | (solve | cases run) | (solve | cases run; rfl) | split at run

private theorem fold_mark_fields {α β γ : Type} (field : α → γ)
    (step : α → β → Except String α)
    (preserved : ∀ before input after,step before input = .ok after → field after = field before)
    (inputs : List β) {before after : α} (run : inputs.foldlM step before = .ok after) :
    field after = field before := by
  induction inputs generalizing before with
  | nil => cases run; rfl
  | cons input inputs ih =>
    rw [List.foldlM_cons] at run
    cases called : step before input with
    | error message => simp only [called,bind,Except.bind] at run; cases run
    | ok middle =>
      simp only [called,bind,Except.bind] at run
      exact (ih run).trans (preserved before input middle called)

/-- Actual output aliasing and physical-result copies preserve every deferred mark and frontier field. -/
theorem bindResults_mark_fields {ctx : Ctx} {pairs : List (Nat × List Reg)}
    {before after : State} {copies : Array MInst}
    (run : bindResults ctx pairs before = .ok (after,copies)) :
    after.entryColor = before.entryColor ∧ after.color = before.color ∧ after.sunk = before.sunk := by
  have frame : markFields after = markFields before := by
    unfold bindResults at run
    apply fold_mark_fields (fun acc : State × Array MInst => markFields acc.1) _ ?_ pairs run
    intro acc pair next step
    obtain ⟨state,code⟩ := acc
    obtain ⟨value,regs⟩ := pair
    dsimp only at step
    cases mapped : ctx.valueReg? value with
    | none => simp only [mapped] at step; cases step
    | some reg =>
      simp only [mapped] at step
      split at step
      · rename_i _ index cls
        cases aliased : state.setAlias reg (.vreg index cls) with
        | error message => simp only [aliased,bind,Except.bind] at step; cases step
        | ok middle =>
          simp only [aliased,bind,Except.bind,pure,Except.pure] at step
          cases step
          exact alias_mark_fields aliased
      · cases step; rfl
      · cases step
  exact ⟨congrArg Prod.fst frame,congrArg (fun fields => fields.2.1) frame,
    congrArg (fun fields => fields.2.2) frame⟩

end Backend.Stock.Proof.Acquire810
