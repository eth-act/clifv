import FV.Backend.Proof.StockConditionalBodyWitness
import FV.Backend.Proof.StockConditionalCoreDemand

namespace Backend.Stock.Proof.ConditionalValues.BodyWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

/-- The executable complete conditional fixture inhabits branch-to-scan
demand transport through the actual per-successor collection call. -/
theorem conditional_core_demand_witness (X : ExtSem) :
    ∃ result, ∃ (spec : ConditionalBodySpec ConditionalCalls.sourceFunction result
      ConditionalCalls.sourceFunction.blocks[0]! 0 0 7 ⟨1,[7]⟩ ⟨2,[7]⟩
      (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
      Stock.lower ConditionalCalls.sourceFunction = .ok result ∧
      LowerScope ConditionalCalls.sourceFunction ∧ Dominated ConditionalCalls.sourceFunction ∧
      ∀ (value : Nat),spec.origin.emission.state.demand[value]! ≤ spec.core.scan.input.demand[value]! := by
  obtain ⟨result,spec,t,left,ρ',w',run,scope,dominated,rest⟩ := executable_conditional_body_witness X
  exact ⟨result,spec,run,scope,dominated,
    conditional_core_emission_demand rfl spec.coreRun spec.origin⟩

end Backend.Stock.Proof.ConditionalValues.BodyWitness
