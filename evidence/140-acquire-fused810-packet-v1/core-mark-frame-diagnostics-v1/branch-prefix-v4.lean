import FV.Backend.Proof.StockAcquireOutgoingMarkFrame

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch collectOutgoing scanBlock

private theorem map_success {α β : Type} {value : Except String α} {mapped : α → β} {output : β}
    (run : mapped <$> value = .ok output) : ∃ input,value = .ok input ∧ mapped input = output := by
  cases value with
  | error message => cases run
  | ok input => cases run; exact ⟨input,rfl,rfl⟩

private theorem branch_init_sunk {ctx : Ctx} {f : Clif.Function} {term : Clif.Terminator}
    {bi ti : Nat} {targets : Array Nat} {input : State} {branch : Option BranchEmission}
    (isBranch : Bool)
    (run : (if isBranch then some <$> emitBranch ctx f term bi ti targets input else pure none) = .ok branch) :
    ((branch.map (·.state)).getD input).sunk = input.sunk := by
  cases isBranch with
  | false => cases run; rfl
  | true =>
    obtain ⟨emitted,called,equal⟩ := map_success run
    rw [← equal]
    exact emitBranch_sunk called


end Backend.Stock.Proof.Acquire810
