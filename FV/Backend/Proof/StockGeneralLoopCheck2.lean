import FV.Backend.Proof.StockGeneralLoopDomain2
import FV.Backend.Proof.StockScalarCodeDomain
import FV.Backend.Proof.StockScalarCheck

/-! The selectors and checkers of the two loop classes with plain computed conditions are sound
(#140, CB-11).

`GeneralArgsLoopCfg2.sourceOk` derives the facts of `domainAt_of_general_args_loop_cfg`
(`source_leaf_eligible_facts`), and its checker accepts the edge split of the actual lowering, so
it derives the code domain of the published split code, as
`ComparisonComputedArgsLoopCfg.check_sound`. `GeneralLoopCfg2.sourceOk` derives the facts of
`domain_of_general_loop_cfg`, and its checker accepts the unsplit code of the actual lowering, as
`ComparisonGeneralLoopCfg.check_sound`. -/

namespace Backend.Stock.GeneralArgsLoopCfg2
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

/-- An ABI of narrow-eligible parameters and returns has no `sret` return. -/
theorem ordinary_of_narrow {f : Clif.Function} (params : f.sig.params.all Scalar.narrowAbiEligible = true)
    (returns : f.sig.returns.all Scalar.narrowAbiEligible = true) :
    (sigRets f.sig).any (·.purpose == .sret) = false := by
  have noSret : f.sig.params.find? (·.purpose == .sret) = none := by
    apply List.find?_eq_none.mpr
    intro p member
    simp [(ordinary_params params) p member]
  rw [sigRets,noSret]
  apply Bool.eq_false_iff.mpr
  intro any
  obtain ⟨p,member,sret⟩ := List.any_eq_true.mp any
  simpa [(ordinary_params returns) p member] using sret

/-- Original input conditions and the split selector derive the per-successor production
domain. -/
theorem domainAt_of_source_leaf_eligible {f : Clif.Function} (checked : sourceLeafEligible f = true)
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true) : Scalar.DomainAt f := by
  obtain ⟨terms,entryKind,family,params,returns⟩ := source_leaf_eligible_facts checked
  exact Proof.GeneralArgsLoopCfg2.domainAt_of_general_args_loop_cfg scope dominated abi
    (ordinary_of_narrow params returns) terms entryKind family

/-- **The split selector is sound.** -/
theorem source_ok_sound {f : Clif.Function} (checked : sourceOk f = true) : Scalar.DomainAt f := by
  simp only [sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨eligible,scope⟩,dominated⟩,abi⟩ := checked
  exact domainAt_of_source_leaf_eligible eligible (lowerScope_of scope) (dominated_of dominated) abi

/-- **The split checker is sound.** The executable check derives the code domain of the published
split code. -/
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

end Backend.Stock.GeneralArgsLoopCfg2

namespace Backend.Stock.GeneralLoopCfg2
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Original input conditions and the legacy selector derive the unchanged production domain. -/
theorem domain_of_source_leaf_eligible {f : Clif.Function} (checked : sourceLeafEligible f = true)
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true) : Scalar.Domain f := by
  obtain ⟨terms,entryKind,family,params,returns⟩ := source_leaf_eligible_facts checked
  exact Proof.GeneralArgsLoopCfg2.domain_of_general_loop_cfg scope dominated abi
    (GeneralArgsLoopCfg2.ordinary_of_narrow params returns) terms entryKind family

/-- **The legacy selector is sound.** -/
theorem source_ok_sound {f : Clif.Function} (checked : sourceOk f = true) : Scalar.Domain f := by
  simp only [sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨eligible,scope⟩,dominated⟩,abi⟩ := checked
  exact domain_of_source_leaf_eligible eligible (lowerScope_of scope) (dominated_of dominated) abi

/-- **The legacy checker is sound.** The executable check derives the unchanged production domain
of the published unsplit code. -/
theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    ∃ result,Scalar.Domain f ∧ Stock.lower f = .ok result ∧ result.code = vc := by
  simp only [check,Bool.and_eq_true] at checked
  obtain ⟨source,lowered⟩ := checked
  cases run : Stock.lower f with
  | error message => simp [run] at lowered
  | ok result =>
    simp only [run,decide_eq_true_eq] at lowered
    exact ⟨result,source_ok_sound source,rfl,lowered⟩

end Backend.Stock.GeneralLoopCfg2
