import FV.Backend.Proof.StockComparisonComputedArgsLoopDomain
import FV.Backend.Proof.StockScalarCodeDomain
import FV.Backend.Proof.StockScalarCheck

/-! The selector and checker of the loop class with computed comparisons and block arguments are
sound (#140, CB-9). `ComparisonComputedArgsLoopCfg.sourceOk` derives the terminator, body and ABI
facts of `domainAt_of_computed_args_loop_cfg` (`source_leaf_eligible_facts`); its targets need no
rank. The checker accepts the edge split of the actual lowering, so it derives the code domain of
the published split code, as `ComparisonArgsLoopCfg.check_sound`. -/

namespace Backend.Stock.ComparisonComputedArgsLoopCfg
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

/-- Original input conditions and the selector derive the per-successor production domain. -/
theorem domainAt_of_source_leaf_eligible {f : Clif.Function} (checked : sourceLeafEligible f = true)
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true) : Scalar.DomainAt f := by
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
  exact Proof.ComparisonComputedArgsLoopCfg.domainAt_of_computed_args_loop_cfg scope dominated abi ordinary terms
    entryKind family

/-- **The selector is sound.** -/
theorem source_ok_sound {f : Clif.Function} (checked : sourceOk f = true) : Scalar.DomainAt f := by
  simp only [sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨eligible,scope⟩,dominated⟩,abi⟩ := checked
  exact domainAt_of_source_leaf_eligible eligible (lowerScope_of scope) (dominated_of dominated) abi

/-- **The checker is sound.** The executable check derives the code domain of the published split
code. -/
theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    Scalar.CodeDomain f vc := by
  simp only [check,Bool.and_eq_true] at checked
  obtain ⟨source,lowered⟩ := checked
  cases run : Stock.lower f with
  | error message => simp [run] at lowered
  | ok result =>
    simp only [run] at lowered
    cases splitRun : splitEdgesChecked result.code result.edgeArgs with
    | error message => simp [splitRun] at lowered
    | ok split =>
      simp only [splitRun,decide_eq_true_eq] at lowered
      subst vc
      exact (source_ok_sound source).code run splitRun

end Backend.Stock.ComparisonComputedArgsLoopCfg
