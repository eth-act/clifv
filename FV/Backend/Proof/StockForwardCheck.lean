import FV.Backend.Lowering.StockForwardCfg
import FV.Backend.Proof.StockForwardDomain
import FV.Backend.Proof.StockForwardLeaf
import FV.Backend.Proof.StockScalarCheck

namespace Backend.Stock.ForwardCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem control_sound {f : Clif.Function} {bi : Nat} {term : Clif.Terminator}
    (checked : controlEligible f bi term = true) :
    (∃ bc target,term = .jump bc ∧ f.blocks.findIdx? (·.id == bc.block) = some target ∧ bi < target) ∨
      (∃ xs,term = .ret xs) := by
  cases term <;> simp only [controlEligible] at checked
  case jump bc =>
    cases target : f.blocks.findIdx? (·.id == bc.block) with
    | none => simp only [target] at checked; cases checked
    | some ti =>
      simp only [target,decide_eq_true_eq] at checked
      exact Or.inl ⟨bc,ti,rfl,target,checked⟩
  case ret xs => exact Or.inr ⟨xs,rfl⟩
  all_goals cases checked

private theorem control_leaf_sound {f : Clif.Function} {bi : Nat} {term : Clif.Terminator}
    (checked : controlLeafEligible f bi term = true) :
    (∃ bc target,term = .jump bc ∧ f.blocks.findIdx? (·.id == bc.block) = some target ∧ bi < target) ∨
      (∃ xs,term = .ret xs) ∨ (∃ c,term = .trap c) := by
  cases term
  case trap c => exact Or.inr (Or.inr ⟨c,rfl⟩)
  all_goals
    rcases control_sound (by simpa only [controlLeafEligible] using checked) with jump | ret
    · exact Or.inl jump
    · exact Or.inr (Or.inl ret)

private theorem normal_abi {params : List Clif.AbiParam}
    (all : params.all Scalar.narrowAbiEligible = true) : ∀ p ∈ params,p.purpose = .normal := by
  intro p member
  have good := List.all_eq_true.mp all p member
  simp only [Scalar.narrowAbiEligible,Bool.and_eq_true] at good
  exact beq_iff_eq.mp good.1

/-- The executable source predicate derives the unchanged universal production
contract. Source ordering, scans and demand transfer are all proved internally. -/
theorem domain_of_eligible {f : Clif.Function} (checked : eligible f = true)
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true) : Scalar.Domain f := by
  unfold eligible at checked
  split at checked
  next entry rest blocks =>
    split at checked
    next bc jump =>
      simp only [Bool.and_eq_true] at checked
      obtain ⟨⟨⟨controls,bodies⟩,params⟩,returns⟩ := checked
      have atControl : ∀ bi b,f.blocks[bi]? = some b → controlEligible f bi b.term = true := by
        intro bi b found
        exact List.all_eq_true.mp controls (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
      have terms : ForwardSource.JumpReturnBlocks f := by
        intro b member
        obtain ⟨bi,bound,found⟩ := List.getElem_of_mem member
        have checked := control_sound (atControl bi b (List.getElem?_eq_some_iff.mpr ⟨bound,found⟩))
        rcases checked with ⟨bc,ti,jump,found,less⟩ | ret
        · exact Or.inl ⟨bc,jump⟩
        · exact Or.inr ret
      have ranked : ForwardSource.Ranked f (fun bi => bi) := by
        intro bi b ti destination found present target
        change bi < ti
        rcases control_sound (atControl bi b found) with ⟨bc,next,jump,identified,less⟩ | ⟨xs,ret⟩
        · simp only [jump,destinations,List.mem_singleton] at present
          subst destination
          have same : next = ti := Option.some.inj (identified.symm.trans target)
          simpa only [same] using less
        · simp only [ret,destinations] at present; cases present
      have family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
        intro b member stm present
        exact Scalar.maskMixedBodyEligible_sound (List.all_eq_true.mp (List.all_eq_true.mp bodies b member) stm present)
      have noSret : f.sig.params.find? (·.purpose == .sret) = none := by
        apply List.find?_eq_none.mpr
        intro p member
        simp [(normal_abi params) p member]
      have ordinary : (sigRets f.sig).any (·.purpose == .sret) = false := by
        rw [sigRets,noSret]
        apply Bool.eq_false_iff.mpr
        intro any
        obtain ⟨p,member,sret⟩ := List.any_eq_true.mp any
        simpa [(normal_abi returns) p member] using sret
      exact Scalar.domain_of_forward_cfg scope dominated abi ordinary ranked terms family
        (by simp only [blocks,List.getElem?_cons_zero]) jump
    all_goals cases checked
  next => cases checked

/-- The same for the leaf selector: blocks may also end in `trap`. -/
theorem domain_of_leafEligible {f : Clif.Function} (checked : leafEligible f = true)
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true) : Scalar.Domain f := by
  unfold leafEligible at checked
  split at checked
  next entry rest blocks =>
    split at checked
    next bc jump =>
      simp only [Bool.and_eq_true] at checked
      obtain ⟨⟨⟨controls,bodies⟩,params⟩,returns⟩ := checked
      have atControl : ∀ bi b,f.blocks[bi]? = some b → controlLeafEligible f bi b.term = true := by
        intro bi b found
        exact List.all_eq_true.mp controls (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
      have terms : ForwardSource.JumpLeafBlocks f := by
        intro b member
        obtain ⟨bi,bound,found⟩ := List.getElem_of_mem member
        rcases control_leaf_sound (atControl bi b (List.getElem?_eq_some_iff.mpr ⟨bound,found⟩)) with
          ⟨bc,ti,jump,found,less⟩ | ret | trap
        · exact Or.inl ⟨bc,jump⟩
        · exact Or.inr (Or.inl ret)
        · exact Or.inr (Or.inr trap)
      have ranked : ForwardSource.Ranked f (fun bi => bi) := by
        intro bi b ti destination found present target
        change bi < ti
        rcases control_leaf_sound (atControl bi b found) with ⟨bc,next,jump,identified,less⟩ | ⟨xs,ret⟩ | ⟨c,trap⟩
        · simp only [jump,destinations,List.mem_singleton] at present
          subst destination
          have same : next = ti := Option.some.inj (identified.symm.trans target)
          simpa only [same] using less
        · simp only [ret,destinations] at present; cases present
        · simp only [trap,destinations] at present; cases present
      have family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
        intro b member stm present
        exact Scalar.maskMixedBodyEligible_sound (List.all_eq_true.mp (List.all_eq_true.mp bodies b member) stm present)
      have noSret : f.sig.params.find? (·.purpose == .sret) = none := by
        apply List.find?_eq_none.mpr
        intro p member
        simp [(normal_abi params) p member]
      have ordinary : (sigRets f.sig).any (·.purpose == .sret) = false := by
        rw [sigRets,noSret]
        apply Bool.eq_false_iff.mpr
        intro any
        obtain ⟨p,member,sret⟩ := List.any_eq_true.mp any
        simpa [(normal_abi returns) p member] using sret
      exact Scalar.domain_of_forward_leaf_cfg scope dominated abi ordinary ranked terms family
        (by simp only [blocks,List.getElem?_cons_zero]) jump
    all_goals cases checked
  next => cases checked

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

end Backend.Stock.ForwardCfg
