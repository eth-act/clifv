import FV.Backend.Proof.StockAcquireBranchMarkFrame
import FV.Backend.Proof.StockTerminalBlocks

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] branchArgs

/-- Actual outgoing argument collection changes demands but preserves the complete sunk array. -/
theorem outgoingStep_sunk {ctx : Ctx} {order : Order} {bi : Nat}
    {before after : State × Array (Array Reg)} {target : Nat × Nat}
    (run : outgoingStep ctx order bi before target = .ok after) : after.1.sunk = before.1.sunk := by
  unfold outgoingStep at run
  split at run
  · cases run; rfl
  · cases called : branchArgs ctx before.1 bi target.2 with
    | error message => simp only [called,bind,Except.bind] at run; cases run
    | ok result =>
      obtain ⟨args,next⟩ := result
      simp only [called,bind,Except.bind,pure,Except.pure] at run
      cases run
      exact Coverage.stock_branchArgs_sunk called

private theorem fold_sunk {ctx : Ctx} {order : Order} {bi : Nat} (targets : List (Nat × Nat))
    {before after : State × Array (Array Reg)}
    (run : targets.foldlM (outgoingStep ctx order bi) before = .ok after) : after.1.sunk = before.1.sunk := by
  induction targets generalizing before with
  | nil => cases run; rfl
  | cons target targets ih =>
    rw [List.foldlM_cons] at run
    cases called : outgoingStep ctx order bi before target with
    | error message => simp only [called,bind,Except.bind] at run; cases run
    | ok middle =>
      simp only [called,bind,Except.bind] at run
      exact (ih run).trans (outgoingStep_sunk called)

/-- The complete real successor-demand collection retains all original read marks. -/
theorem collectOutgoing_sunk {ctx : Ctx} {order : Order} {bi : Nat} {targets : Array Nat}
    {before : State} {after : State × Array (Array Reg)}
    (run : collectOutgoing ctx order bi targets before = .ok after) : after.1.sunk = before.sunk :=
  fold_sunk _ run

end Backend.Stock.Proof.Acquire810
