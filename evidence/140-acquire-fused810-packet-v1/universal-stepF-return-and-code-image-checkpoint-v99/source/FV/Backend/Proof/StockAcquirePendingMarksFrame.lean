import FV.Backend.Proof.StockAcquirePendingMarks
import FV.Backend.Proof.StockAcquirePendingFrame
import FV.Backend.Proof.StockPureUnsunk

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

private theorem delegated_sunk {ctx : Ctx} {term : Term} {args : List V}
    {before after : State} {out : V}
    (run : (match Backend.externCtor ctx term args before.base with
      | .ok (value,base) => ExtResult.ok (value,{before with base})
      | .fail => ExtResult.fail
      | .unmodeled message => ExtResult.unmodeled message) = ExtResult.ok (out,after)) :
    after.sunk = before.sunk := by
  cases call : Backend.externCtor ctx term args before.base with
  | fail => rw [call] at run; cases run
  | unmodeled message => rw [call] at run; cases run
  | ok pair =>
    obtain ⟨value,base⟩ := pair
    rw [call] at run
    cases run
    rfl

/-- Every constructor outside the actual sink shape preserves all deferred marks. -/
theorem stock_ctor_sunk_without_sink_shape {ctx : Ctx} {term : Term} {args : List V}
    {before after : State} {out : V}
    (shape : ¬ (term.id = TId.sink_inst ∧ ∃ producer,args = [.inst producer]))
    (run : Stock.externCtor ctx term args before = .ok (out,after)) : after.sunk = before.sunk := by
  by_cases idEq : term.id = TId.sink_inst
  · have wrong : ¬ ∃ producer,args = [.inst producer] := fun actual => shape ⟨idEq,actual⟩
    cases args with
    | nil =>
      simp only [Stock.externCtor,idEq] at run
      split at run <;> cases run <;> rfl
    | cons first rest =>
      cases rest with
      | nil =>
        cases first <;> first
          | exact False.elim (wrong ⟨_,rfl⟩)
          | simp only [Stock.externCtor,idEq] at run
            split at run <;> cases run <;> rfl
      | cons second rest =>
        simp only [Stock.externCtor,idEq] at run
        split at run <;> cases run <;> rfl

  · exact stock_ctor_noSink idEq run

end Backend.Stock.Proof.Acquire810
