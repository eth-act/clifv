import FV.Backend.Proof.StockAcquireOutgoingMarkFrame

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch collectOutgoing scanBlock

private theorem branch_init_sunk {ctx : Ctx} {f : Clif.Function} {term : Clif.Terminator}
    {bi ti : Nat} {targets : Array Nat} {input : State} {branch : Option BranchEmission}
    (isBranch : Bool)
    (run : (if isBranch then some <$> emitBranch ctx f term bi ti targets input else pure none) = .ok branch) :
    ((branch.map (·.state)).getD input).sunk = input.sunk := by
  cases isBranch with
  | false => cases run; rfl
  | true =>
    cases called : emitBranch ctx f term bi ti targets input with
    | error message => simp only [called,Functor.map,Except.map] at run; cases run
    | ok emitted =>
      simp only [called,Functor.map,Except.map] at run
      cases run
      exact emitBranch_sunk called


end Backend.Stock.Proof.Acquire810
