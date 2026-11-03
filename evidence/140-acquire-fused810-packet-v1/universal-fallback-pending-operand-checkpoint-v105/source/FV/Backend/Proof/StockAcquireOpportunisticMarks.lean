import FV.Backend.Proof.StockAcquirePendingRecordMarks

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

private def sunkFields (state : State) := state.sunk

private theorem alias_sunk {before after : State} {dst src : Reg}
    (run : before.setAlias dst src = .ok after) : sunkFields after = sunkFields before := by
  cases dst <;> cases src <;>
    simp only [State.setAlias,bind,Except.bind,pure,Except.pure,
      throw,throwThe,MonadExceptOf.throw] at run
  all_goals repeat' first | (solve | cases run) | (solve | cases run; rfl) | split at run

private theorem fold_sunk {α β γ : Type} (field : α → γ)
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

/-- Committing actual opportunistic aliases preserves the full sunk array. -/
theorem opportunisticValues_sunk {ctx : Ctx} {values : List Nat} {before after : State}
    (run : commitOpportunisticValues ctx values before = .ok after) : after.sunk = before.sunk := by
  unfold commitOpportunisticValues at run
  apply fold_sunk sunkFields _ ?_ values run
  intro state value next step
  split at step
  · split at step
    · rename_i dst mapped
      split at step
      · rename_i src _
        cases aliased : state.setAlias dst src with
        | error message => simp only [aliased,bind,Except.bind] at step; cases step
        | ok middle =>
          simp only [aliased,bind,Except.bind,pure,Except.pure] at step
          cases step
          exact alias_sunk (after := middle) aliased
      · cases step
    · cases step
  · cases step; rfl

/-- The actual opportunistic scan branch cannot clear or create deferred marks. -/
theorem opportunistic_sunk {ctx : Ctx} {block inst : Nat} {before after : State}
    (run : commitOpportunistic ctx block inst before = .ok (some after)) : after.sunk = before.sunk := by
  unfold commitOpportunistic at run
  dsimp only at run
  split at run
  · cases run
  · cases called : commitOpportunisticValues ctx (ctx.insts[inst]!.results) before with
    | error message => simp only [called,bind,Except.bind] at run; cases run
    | ok middle =>
      simp only [called,bind,Except.bind,pure,Except.pure] at run
      cases run
      exact opportunisticValues_sunk called

end Backend.Stock.Proof.Acquire810
