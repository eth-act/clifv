import FV.Backend.Lowering.StockParameterCfg
import FV.Backend.Proof.StockParameterDomain
import FV.Backend.Proof.StockScalarCheck

namespace Backend.Stock.ParameterCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.ParameterCfg
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem parameter_eligible_sound {f : Clif.Function} {c : Nat}
    (checked : parameterEligible f c = true) : ParameterCondition f c := by
  obtain ⟨b,member,eligible⟩ := List.any_eq_true.mp checked
  obtain ⟨bi,block⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨pair,parameter,good⟩ := List.any_eq_true.mp eligible
  obtain ⟨value,ty⟩ := pair
  change (value == c && (ty == .i32 || ty == .i64)) = true at good
  simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at good
  obtain ⟨same,wide⟩ := good
  subst value
  exact ⟨bi,b,ty,block,parameter,wide⟩

private theorem target_after_sound {f : Clif.Function} {bi : Nat} {bc : Clif.BlockCall}
    (checked : targetAfter f bi bc = true) :
    ∃ ti,f.blocks.findIdx? (·.id == bc.block) = some ti ∧ bi < ti := by
  simp only [targetAfter] at checked
  cases target : f.blocks.findIdx? (·.id == bc.block) with
  | none => simp only [target] at checked; cases checked
  | some ti => simp only [target,decide_eq_true_eq] at checked; exact ⟨ti,rfl,checked⟩

private theorem control_facts {f : Clif.Function} {bi : Nat} {term : Clif.Terminator}
    (checked : controlEligible f bi term = true) :
    ((∃ bc,term = .jump bc) ∨ (∃ xs,term = .ret xs) ∨
      ∃ c yes no,term = .brif c yes no ∧ yes.args = [] ∧ no.args = [] ∧ ParameterCondition f c) ∧
    ∀ (ti : Nat) (destination : Nat × List Clif.TryArg),destination ∈ destinations term →
      f.blocks.findIdx? (·.id == destination.1) = some ti → bi < ti := by
  cases term <;> simp only [controlEligible] at checked
  case jump bc =>
    obtain ⟨target,lookup,later⟩ := target_after_sound checked
    refine ⟨Or.inl ⟨bc,rfl⟩,?_⟩
    intro ti destination present target
    simp only [destinations,List.mem_singleton] at present
    subst destination
    have same := Option.some.inj (lookup.symm.trans target)
    simpa only [same] using later
  case ret xs =>
    refine ⟨Or.inr (Or.inl ⟨xs,rfl⟩),?_⟩
    intro ti destination present target
    simp only [destinations] at present; cases present
  case brif c yes no =>
    simp only [Bool.and_eq_true] at checked
    obtain ⟨⟨⟨⟨parameter,yesEmpty⟩,noEmpty⟩,yesGood⟩,noGood⟩ := checked
    refine ⟨Or.inr (Or.inr ⟨c,yes,no,rfl,List.isEmpty_iff.mp yesEmpty,List.isEmpty_iff.mp noEmpty,
      parameter_eligible_sound parameter⟩),?_⟩
    intro ti destination present target
    simp only [destinations,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl
    · obtain ⟨next,lookup,later⟩ := target_after_sound yesGood
      have same := Option.some.inj (lookup.symm.trans target)
      simpa only [same] using later
    · obtain ⟨next,lookup,later⟩ := target_after_sound noGood
      have same := Option.some.inj (lookup.symm.trans target)
      simpa only [same] using later
  all_goals cases checked

/-- Source control, parameter provenance, ranking and body families are derived by the selector. -/
theorem source_eligible_facts {f : Clif.Function} (checked : sourceEligible f = true) :
    ParameterTerms f ∧ ForwardSource.Ranked f id ∧
    (∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst) ∧
    f.sig.params.all Scalar.narrowAbiEligible = true ∧ f.sig.returns.all Scalar.narrowAbiEligible = true := by
  simp only [sourceEligible,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨controls,bodies⟩,params⟩,returns⟩ := checked
  have each : ∀ (bi : Nat) (b : Clif.Block),f.blocks[bi]? = some b → controlEligible f bi b.term = true := by
    intro bi b found
    exact List.all_eq_true.mp controls (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
  refine ⟨?_,?_,?_,params,returns⟩
  · intro bi b found
    exact (control_facts (each bi b found)).1
  · intro bi b ti destination found present target
    exact (control_facts (each bi b found)).2 ti destination present target
  · intro b member stm present
    exact Scalar.maskMixedBodyEligible_sound (List.all_eq_true.mp (List.all_eq_true.mp bodies b member) stm present)

private theorem ordinary_params {params : List Clif.AbiParam}
    (all : params.all Scalar.narrowAbiEligible = true) : ∀ p ∈ params,p.purpose = .normal := by
  intro p member
  have good := List.all_eq_true.mp all p member
  simp only [Scalar.narrowAbiEligible,Bool.and_eq_true] at good
  exact beq_iff_eq.mp good.1

/-- Original input conditions and the source selector derive the unchanged production domain. -/
theorem domain_of_source_eligible {f : Clif.Function} (checked : sourceEligible f = true)
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true) : Scalar.Domain f := by
  obtain ⟨terms,ranked,family,params,returns⟩ := source_eligible_facts checked
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
  exact domain_of_parameter_cfg scope dominated abi ordinary ranked terms family

theorem source_ok_sound {f : Clif.Function} (checked : sourceOk f = true) : Scalar.Domain f := by
  simp only [sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨eligible,scope⟩,dominated⟩,abi⟩ := checked
  exact domain_of_source_eligible eligible (lowerScope_of scope) (dominated_of dominated) abi

theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    ∃ result,Scalar.Domain f ∧ Stock.lower f = .ok result ∧ result.code = vc := by
  simp only [check,Bool.and_eq_true] at checked
  obtain ⟨source,lowered⟩ := checked
  cases run : Stock.lower f with
  | error message => simp [run] at lowered
  | ok result =>
    simp only [run,decide_eq_true_eq] at lowered
    exact ⟨result,source_ok_sound source,rfl,lowered⟩
end Backend.Stock.ParameterCfg
