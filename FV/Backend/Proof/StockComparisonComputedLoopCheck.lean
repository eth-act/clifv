import FV.Backend.Proof.StockComparisonComputedLoopDomain

/-! The computed comparison loop selector and checker are sound for the unchanged production
domain (#140, CB-8). `ComparisonComputedLoopCfg.sourceOk` derives the facts of
`domain_of_computed_loop_cfg` (`source_leaf_eligible_facts`). -/

namespace Backend.Stock.ComparisonComputedLoopCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem ordinary_params {params : List Clif.AbiParam}
    (all : params.all Scalar.narrowAbiEligible = true) : ∀ p ∈ params,p.purpose = .normal := by
  intro p member
  have good := List.all_eq_true.mp all p member
  simp only [Scalar.narrowAbiEligible,Bool.and_eq_true] at good
  exact beq_iff_eq.mp good.1

/-- Original input conditions and the computed comparison loop selector derive the unchanged production
domain. -/
theorem domain_of_source_leaf_eligible {f : Clif.Function} (checked : sourceLeafEligible f = true)
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true) : Scalar.Domain f := by
  obtain ⟨terms,entryKind,family,params,returns⟩ := source_leaf_eligible_facts checked
  have noSret : f.sig.params.find? (·.purpose == .sret) = none := by
    apply List.find?_eq_none.mpr
    intro p member
    simp [(ordinary_params params) p member]
  have ordinary : (sigRets f.sig).any (·.purpose == .sret) = false := by
    rw [sigRets,noSret]
    apply Bool.eq_false_iff.mpr
    intro any
    obtain ⟨p,member,sret⟩ := List.any_eq_true.mp any
    simpa [(ordinary_params returns) p member] using sret
  exact Proof.ComparisonComputedLoopCfg.domain_of_computed_loop_cfg scope dominated abi ordinary terms entryKind family

theorem source_ok_sound {f : Clif.Function} (checked : sourceOk f = true) : Scalar.Domain f := by
  simp only [sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨eligible,scope⟩,dominated⟩,abi⟩ := checked
  exact domain_of_source_leaf_eligible eligible (lowerScope_of scope) (dominated_of dominated) abi

theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    ∃ result,Scalar.Domain f ∧ Stock.lower f = .ok result ∧ result.code = vc := by
  simp only [check,Bool.and_eq_true] at checked
  obtain ⟨source,lowered⟩ := checked
  cases run : Stock.lower f with
  | error message => simp [run] at lowered
  | ok result =>
    simp only [run,decide_eq_true_eq] at lowered
    exact ⟨result,source_ok_sound source,rfl,lowered⟩

end Backend.Stock.ComparisonComputedLoopCfg
