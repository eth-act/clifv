module

public import FV.Backend.Proof.StockConditionalCoreOrigin
public import FV.Backend.Proof.StockCfgTraversalDemand

@[expose] public section

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch collectOutgoing scanBlock

/-- Actual outgoing argument collection preserves every demand installed by
the separately emitted conditional branch. This connects the branch's output
contract to the real backward scan input, including per-successor edges. -/
theorem conditional_core_emission_demand {ctx : Ctx} {order : Order} {f : Clif.Function}
    {b : Clif.Block} {bi start stop : Nat} {data : V} {targets : Array Nat}
    {input : State} {core : LoweredBlockCore} {c : Nat} {yes no : Clif.BlockCall}
    (term : b.term = .brif c yes no)
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok core)
    (origin : CoreOrigin
      {Driver.termCtx ctx (stop-1) data with tryRegs := input.tryRegs[stop-1]!}
      f bi (stop-1) targets input core) :
    ∀ (value : Nat),origin.emission.state.demand[value]! ≤ core.scan.input.demand[value]! := by
  obtain ⟨emission,afterEdges,retained,branchCall,outgoing,scanInput,scanCtx,branchScan,combined⟩ :=
    conditional_core_calls term run
  have same : emission = origin.emission := Option.some.inj (retained.symm.trans origin.retained)
  intro value
  rw [scanInput,← same]
  exact CfgDemand.outgoing_demand_mono outgoing value

end Backend.Stock.Proof.ConditionalValues
