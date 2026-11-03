import FV.Backend.Proof.StockConditionalDomain

namespace Backend.Stock.ConditionalCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem normal_abi {params : List Clif.AbiParam}
    (all : params.all Scalar.narrowAbiEligible = true) : ∀ p ∈ params,p.purpose = .normal := by
  intro p member
  have good := List.all_eq_true.mp all p member
  simp only [Scalar.narrowAbiEligible,Bool.and_eq_true] at good
  exact beq_iff_eq.mp good.1

/-- Original source checks and the conditional selector derive the unchanged
production contract. Returns/traps, ABI entry and compatibility are internal. -/
theorem domain_of_eligible {f : Clif.Function} (eligible : eligible f = true)
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true) : Scalar.Domain f := by
  obtain ⟨shape⟩ := eligible_shape eligible
  have noSret : f.sig.params.find? (·.purpose == .sret) = none := by
    apply List.find?_eq_none.mpr
    intro p member
    simp [(normal_abi shape.abiParams) p member]
  have ordinary : (sigRets f.sig).any (·.purpose == .sret) = false := by
    rw [sigRets,noSret]
    apply Bool.eq_false_iff.mpr
    intro any
    obtain ⟨p,member,sret⟩ := List.any_eq_true.mp any
    simpa [(normal_abi shape.abiReturns) p member] using sret
  exact domain_of_shape shape scope dominated abi ordinary

/-- The same for the leaf selector: each nonentry block returns or ends in `trap`. -/
theorem domain_of_leafEligible {f : Clif.Function} (eligible : leafEligible f = true)
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true) : Scalar.Domain f := by
  obtain ⟨shape⟩ := leafEligible_shape eligible
  have noSret : f.sig.params.find? (·.purpose == .sret) = none := by
    apply List.find?_eq_none.mpr
    intro p member
    simp [(normal_abi shape.abiParams) p member]
  have ordinary : (sigRets f.sig).any (·.purpose == .sret) = false := by
    rw [sigRets,noSret]
    apply Bool.eq_false_iff.mpr
    intro any
    obtain ⟨p,member,sret⟩ := List.any_eq_true.mp any
    simpa [(normal_abi shape.abiReturns) p member] using sret
  exact domain_of_leafShape shape scope dominated abi ordinary

theorem sourceOk_sound {f : Clif.Function} (checked : sourceOk f = true) : Scalar.Domain f := by
  simp only [sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨eligible,scope⟩,dominated⟩,abi⟩ := checked
  exact domain_of_leafEligible eligible (lowerScope_of scope) (dominated_of dominated) abi

theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    ∃ result,Scalar.Domain f ∧ Stock.lower f = .ok result ∧ result.code = vc := by
  simp only [check,Bool.and_eq_true] at checked
  obtain ⟨source,lowered⟩ := checked
  cases run : Stock.lower f with
  | error message => simp [run] at lowered
  | ok result =>
    simp only [run,decide_eq_true_eq] at lowered
    exact ⟨result,sourceOk_sound source,rfl,lowered⟩

end Backend.Stock.ConditionalCfg
