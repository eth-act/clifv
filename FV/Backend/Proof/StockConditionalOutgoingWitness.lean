module

public import FV.Backend.Proof.StockOutgoingFrame
public import FV.Backend.Proof.StockConditionalBodyWitness

@[expose] public section

namespace Backend.Stock.Proof.ConditionalValues.BodyWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

/-- The actual nonempty per-successor collection of the complete executable
conditional fixture preserves the branch base and demand extent at scan entry. -/
theorem conditional_outgoing_frame_witness (X : ExtSem) :
    ∃ result, ∃ (spec : ConditionalBodySpec ConditionalCalls.sourceFunction result
      ConditionalCalls.sourceFunction.blocks[0]! 0 0 7 ⟨1,[7]⟩ ⟨2,[7]⟩
      (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
      ∃ afterEdges,
      Stock.lower ConditionalCalls.sourceFunction = .ok result ∧
      LowerScope ConditionalCalls.sourceFunction ∧ Dominated ConditionalCalls.sourceFunction ∧
      collectOutgoing result.ctx result.order 0 result.order.successors[0]!
        spec.origin.emission.state = .ok (afterEdges,spec.core.outgoing) ∧
      afterEdges.base = spec.origin.emission.state.base ∧
      afterEdges.demand.size = spec.origin.emission.state.demand.size ∧
      spec.core.scan.input.base = spec.origin.emission.state.base ∧
      spec.core.scan.input.demand.size = spec.origin.emission.state.demand.size := by
  obtain ⟨result,spec,t,left,ρ',w',run,scope,dominated,rest⟩ := executable_conditional_body_witness X
  obtain ⟨emission,afterEdges,retained,branchCall,outgoing,scanInput,scanCtx,branchScan,combined⟩ :=
    conditional_core_calls rfl spec.coreRun
  have same : emission = spec.origin.emission := Option.some.inj (retained.symm.trans spec.origin.retained)
  rw [same] at outgoing
  obtain ⟨base,extent⟩ := outgoing_base_extent outgoing
  refine ⟨result,spec,afterEdges,run,scope,dominated,outgoing,base,extent,?_,?_⟩
  · rw [scanInput]
    exact base
  · rw [scanInput]
    exact extent

end Backend.Stock.Proof.ConditionalValues.BodyWitness
