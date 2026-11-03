import FV.Backend.Proof.StockAcquireReadMarked

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem bind_success {α β : Type} {value : Except String α}
    {next : α → Except String β} {output : β}
    (run : (value >>= next) = .ok output) : ∃ input,value = .ok input ∧ next input = .ok output := by
  cases value with
  | error message => cases run
  | ok input => exact ⟨input,rfl,run⟩

/-- A real sink cannot start from an uninitialized source-color frontier. -/
theorem PendingMarks.none_empty {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : PendingMarks ctx before pending after) (color : before.color = none) : pending = [] := by
  by_contra nonempty
  obtain ⟨final,afterColor⟩ := trace.nonempty_color_some nonempty
  have initialized := trace.forget.color_distance afterColor
  rw [color] at initialized
  cases initialized

/-- Every successful named evaluator call with no source color preserves all sunk marks. -/
theorem stock_runTerm_none_sunk {ctx : Ctx} {name : String} {args : List V}
    {before after : State} {out : Option V} {trace : List RuleId}
    (color : before.color = none)
    (run : Stock.runTerm ctx name args before = .ok (out,after,trace)) : after.sunk = before.sunk := by
  obtain ⟨pending,marks⟩ := stock_runTerm_pending_marks_execution run
  have empty := marks.none_empty color
  have exactSunk := marks.sunk_exact
  rwa [empty,List.foldl_nil] at exactSunk

/-- The actual separately emitted branch initializes no sink color and preserves every prior mark. -/
theorem emitBranch_sunk {ctx : Ctx} {f : Clif.Function} {term : Clif.Terminator}
    {bi ti : Nat} {targets : Array Nat} {input : State} {output : BranchEmission}
    (run : emitBranch ctx f term bi ti targets input = .ok output) : output.state.sunk = input.sunk := by
  unfold emitBranch at run
  dsimp only at run
  obtain ⟨result,rootRun,rest⟩ := bind_success run
  obtain ⟨out,next,fired⟩ := result
  split at rest
  · cases rest
  · obtain ⟨code,codeRun,finished⟩ := bind_success rest
    have same := Except.ok.inj finished
    have outputState := congrArg (fun emitted : BranchEmission => emitted.state.sunk) same
    exact outputState.symm.trans (stock_runTerm_none_sunk rfl rootRun)

end Backend.Stock.Proof.Acquire810
