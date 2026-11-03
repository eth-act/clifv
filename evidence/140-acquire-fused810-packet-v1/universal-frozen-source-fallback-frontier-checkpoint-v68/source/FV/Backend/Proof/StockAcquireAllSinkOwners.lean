import FV.Backend.Proof.StockAcquireDriverSinkOwners

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] lowerNode

/-- Actual initialization and full traversal derive ownership for all final and inherited marks.
The global mark array is never assumed empty at a later block entry. -/
theorem stock_lower_all_sink_owners {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) :
    (∀ (producer : Nat),result.final.sunk[producer]! = true → SinkOwnedBy f result.blockScans.toList producer) ∧
      EarlierEntryOwners f result.blockScans.toList := by
  have actualRun := run
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  rename_i _ built hbuild _ order horder _ driver hdriver
  have initial : DriverSinkOwners f {
      state := built.2.2
      blocks := Array.replicate order.nodes.size default
      edgeArgs := Array.replicate order.nodes.size #[]
      schedule := #[],scans := #[],blockScans := #[],rules := #[] } := by
    constructor
    · intro producer marked
      have empty := SinkRules.build_ctx_sunk_false hbuild producer
      rw [empty] at marked
      cases marked
    · intro event member
      cases member
  exact stock_lower_actual_nodes_sink_owners actualRun scope hdriver (fun event member => member) initial

end Backend.Stock.Proof.Acquire810
