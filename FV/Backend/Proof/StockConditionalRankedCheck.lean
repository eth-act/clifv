import FV.Backend.Lowering.StockConditionalRankedCfg
import FV.Backend.Proof.StockConditionalRankedDomain
import FV.Backend.Proof.StockForwardLeaf
import FV.Backend.Proof.StockScalarCheck

namespace Backend.Stock.ConditionalCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.ConditionalValues
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem ranked_target_sound {f : Clif.Function} {bc : Clif.BlockCall}
    (checked : targetEligible f bc = true) :
    bc.args = [] ∧ ∃ tl,blockIdx? f bc.block = some tl ∧ 0 < tl := by
  simp only [targetEligible,Bool.and_eq_true] at checked
  have empty : bc.args = [] := List.isEmpty_iff.mp checked.1
  cases lookup : f.blocks.findIdx? (·.id == bc.block) with
  | none => simp only [lookup] at checked; cases checked.2
  | some tl =>
    simp only [lookup,decide_eq_true_eq] at checked
    exact ⟨empty,tl,lookup,checked.2⟩
private theorem ranked_control_sound {f : Clif.Function} {bi : Nat} {term : Clif.Terminator}
    (checked : Backend.Stock.ForwardCfg.controlEligible f bi term = true) :
    (∃ bc target,term = .jump bc ∧ f.blocks.findIdx? (·.id == bc.block) = some target ∧ bi < target) ∨
      (∃ xs,term = .ret xs) := by
  cases term <;> simp only [Backend.Stock.ForwardCfg.controlEligible] at checked
  case jump bc =>
    cases target : f.blocks.findIdx? (·.id == bc.block) with
    | none => simp only [target] at checked; cases checked
    | some ti =>
      simp only [target,decide_eq_true_eq] at checked
      exact Or.inl ⟨bc,ti,rfl,target,checked⟩
  case ret xs => exact Or.inr ⟨xs,rfl⟩
  all_goals cases checked
private theorem ranked_control_leaf_sound {f : Clif.Function} {bi : Nat} {term : Clif.Terminator}
    (checked : Backend.Stock.ForwardCfg.controlLeafEligible f bi term = true) :
    (∃ bc target,term = .jump bc ∧ f.blocks.findIdx? (·.id == bc.block) = some target ∧ bi < target) ∨
      (∃ xs,term = .ret xs) ∨ (∃ c,term = .trap c) := by
  cases term
  case trap c => exact Or.inr (Or.inr ⟨c,rfl⟩)
  all_goals
    rcases ranked_control_sound (by simpa only [Backend.Stock.ForwardCfg.controlLeafEligible] using checked) with jump | ret
    · exact Or.inl jump
    · exact Or.inr (Or.inl ret)
/-- All continuation, ranking and metadata facts come from source syntax. -/
theorem ranked_eligible_shape {f : Clif.Function} (checked : rankedEligible f = true) : Nonempty (RankedShape f) := by
  cases blocks : f.blocks with
  | nil => simp [rankedEligible,blocks] at checked
  | cons entry rest =>
    cases term : entry.term <;> simp only [rankedEligible,blocks,term] at checked
    case brif c yes no =>
      simp only [Bool.and_eq_true] at checked
      obtain ⟨⟨⟨⟨⟨⟨parameter,yesGood⟩,noGood⟩,tails⟩,bodies⟩,params⟩,returns⟩ := checked
      obtain ⟨pair,member,good⟩ := List.any_eq_true.mp parameter
      obtain ⟨value,ty⟩ := pair
      change (value == c && (ty == .i32 || ty == .i64)) = true at good
      simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at good
      obtain ⟨same,wide⟩ := good
      subst value
      have targets : ∀ bc,bc = yes ∨ bc = no → bc.args = [] ∧
          ∃ tl,blockIdx? f bc.block = some tl ∧ 0 < tl := by
        intro bc choice
        rcases choice with rfl | rfl
        · exact ranked_target_sound yesGood
        · exact ranked_target_sound noGood
      have atControl : ∀ bi b,f.blocks[bi]? = some b → bi ≠ 0 →
          Backend.Stock.ForwardCfg.controlEligible f bi b.term = true := by
        intro bi b found nonentry
        cases bi with
        | zero => exact False.elim (nonentry rfl)
        | succ bi =>
          rw [blocks,List.getElem?_cons_succ] at found
          exact List.all_eq_true.mp tails (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
      refine ⟨{
        entry := entry
        condition := c
        yes := yes
        no := no
        source := by simp only [blocks,List.getElem?_cons_zero]
        term := term
        parameter := ⟨ty,member,wide⟩
        targets := targets
        tails := ?_
        ranked := ?_
        family := ?_ }⟩
      · intro bi b found nonentry
        rcases ranked_control_sound (atControl bi b found nonentry) with ⟨bc,ti,jump,lookup,less⟩ | ret
        · exact Or.inl ⟨bc,jump⟩
        · exact Or.inr ret
      · intro bi b ti destination found present target
        change bi < ti
        by_cases isEntry : bi = 0
        · subst bi
          have same : b = entry := Option.some.inj (found.symm.trans (by simp only [blocks,List.getElem?_cons_zero]))
          subst b
          simp only [term,destinations,List.mem_cons,List.not_mem_nil,or_false] at present
          rcases present with rfl | rfl
          · obtain ⟨_,tl,lookup,less⟩ := targets yes (Or.inl rfl)
            have same : tl = ti := Option.some.inj (lookup.symm.trans target)
            simpa only [same] using less
          · obtain ⟨_,tl,lookup,less⟩ := targets no (Or.inr rfl)
            have same : tl = ti := Option.some.inj (lookup.symm.trans target)
            simpa only [same] using less
        · rcases ranked_control_sound (atControl bi b found isEntry) with ⟨bc,next,jump,lookup,less⟩ | ⟨xs,ret⟩
          · simp only [jump,destinations,List.mem_singleton] at present
            subst destination
            have same : next = ti := Option.some.inj (lookup.symm.trans target)
            simpa only [same] using less
          · simp only [ret,destinations] at present; cases present
      · intro b member stm present
        have member' : b ∈ entry :: rest := by simpa only [blocks] using member
        exact Scalar.maskMixedBodyEligible_sound
          (List.all_eq_true.mp (List.all_eq_true.mp bodies b member') stm present)
    all_goals cases checked
/-- The leaf selector derives the leaf shape in the same way. -/
theorem ranked_leaf_eligible_shape {f : Clif.Function} (checked : rankedLeafEligible f = true) : Nonempty (RankedLeafShape f) := by
  cases blocks : f.blocks with
  | nil => simp [rankedLeafEligible,blocks] at checked
  | cons entry rest =>
    cases term : entry.term <;> simp only [rankedLeafEligible,blocks,term] at checked
    case brif c yes no =>
      simp only [Bool.and_eq_true] at checked
      obtain ⟨⟨⟨⟨⟨⟨parameter,yesGood⟩,noGood⟩,tails⟩,bodies⟩,params⟩,returns⟩ := checked
      obtain ⟨pair,member,good⟩ := List.any_eq_true.mp parameter
      obtain ⟨value,ty⟩ := pair
      change (value == c && (ty == .i32 || ty == .i64)) = true at good
      simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at good
      obtain ⟨same,wide⟩ := good
      subst value
      have targets : ∀ bc,bc = yes ∨ bc = no → bc.args = [] ∧
          ∃ tl,blockIdx? f bc.block = some tl ∧ 0 < tl := by
        intro bc choice
        rcases choice with rfl | rfl
        · exact ranked_target_sound yesGood
        · exact ranked_target_sound noGood
      have atControl : ∀ bi b,f.blocks[bi]? = some b → bi ≠ 0 →
          Backend.Stock.ForwardCfg.controlLeafEligible f bi b.term = true := by
        intro bi b found nonentry
        cases bi with
        | zero => exact False.elim (nonentry rfl)
        | succ bi =>
          rw [blocks,List.getElem?_cons_succ] at found
          exact List.all_eq_true.mp tails (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
      refine ⟨{
        entry := entry
        condition := c
        yes := yes
        no := no
        source := by simp only [blocks,List.getElem?_cons_zero]
        term := term
        parameter := ⟨ty,member,wide⟩
        targets := targets
        tails := ?_
        ranked := ?_
        family := ?_ }⟩
      · intro bi b found nonentry
        rcases ranked_control_leaf_sound (atControl bi b found nonentry) with ⟨bc,ti,jump,lookup,less⟩ | ret | trap
        · exact Or.inl ⟨bc,jump⟩
        · exact Or.inr (Or.inl ret)
        · exact Or.inr (Or.inr trap)
      · intro bi b ti destination found present target
        change bi < ti
        by_cases isEntry : bi = 0
        · subst bi
          have same : b = entry := Option.some.inj (found.symm.trans (by simp only [blocks,List.getElem?_cons_zero]))
          subst b
          simp only [term,destinations,List.mem_cons,List.not_mem_nil,or_false] at present
          rcases present with rfl | rfl
          · obtain ⟨_,tl,lookup,less⟩ := targets yes (Or.inl rfl)
            have same : tl = ti := Option.some.inj (lookup.symm.trans target)
            simpa only [same] using less
          · obtain ⟨_,tl,lookup,less⟩ := targets no (Or.inr rfl)
            have same : tl = ti := Option.some.inj (lookup.symm.trans target)
            simpa only [same] using less
        · rcases ranked_control_leaf_sound (atControl bi b found isEntry) with ⟨bc,next,jump,lookup,less⟩ | ⟨xs,ret⟩ | ⟨c,trap⟩
          · simp only [jump,destinations,List.mem_singleton] at present
            subst destination
            have same : next = ti := Option.some.inj (lookup.symm.trans target)
            simpa only [same] using less
          · simp only [ret,destinations] at present; cases present
          · simp only [trap,destinations] at present; cases present
      · intro b member stm present
        have member' : b ∈ entry :: rest := by simpa only [blocks] using member
        exact Scalar.maskMixedBodyEligible_sound
          (List.all_eq_true.mp (List.all_eq_true.mp bodies b member') stm present)
    all_goals cases checked
private theorem ranked_abi {f : Clif.Function} (checked : rankedEligible f = true) :
    f.sig.params.all Scalar.narrowAbiEligible = true ∧ f.sig.returns.all Scalar.narrowAbiEligible = true := by
  cases blocks : f.blocks with
  | nil => simp [rankedEligible,blocks] at checked
  | cons entry rest =>
    cases term : entry.term <;> simp only [rankedEligible,blocks,term] at checked
    case brif c yes no =>
      simp only [Bool.and_eq_true] at checked
      exact ⟨checked.1.2,checked.2⟩
    all_goals cases checked
private theorem ranked_normal_abi {params : List Clif.AbiParam}
    (all : params.all Scalar.narrowAbiEligible = true) : ∀ p ∈ params,p.purpose = .normal := by
  intro p member
  have good := List.all_eq_true.mp all p member
  simp only [Scalar.narrowAbiEligible,Bool.and_eq_true] at good
  exact beq_iff_eq.mp good.1
/-- Source syntax and the original input conditions derive universal correctness. -/
theorem domain_of_ranked_eligible {f : Clif.Function} (checked : rankedEligible f = true)
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true) : Scalar.Domain f := by
  obtain ⟨shape⟩ := ranked_eligible_shape checked
  obtain ⟨params,returns⟩ := ranked_abi checked
  have noSret : f.sig.params.find? (·.purpose == .sret) = none := by
    apply List.find?_eq_none.mpr
    intro p member
    simp [(ranked_normal_abi params) p member]
  have ordinary : (sigRets f.sig).any (·.purpose == .sret) = false := by
    rw [sigRets,noSret]
    apply Bool.eq_false_iff.mpr
    intro any
    obtain ⟨p,member,sret⟩ := List.any_eq_true.mp any
    simpa [(ranked_normal_abi returns) p member] using sret
  exact domain_of_ranked_shape shape scope dominated abi ordinary

private theorem ranked_leaf_abi {f : Clif.Function} (checked : rankedLeafEligible f = true) :
    f.sig.params.all Scalar.narrowAbiEligible = true ∧ f.sig.returns.all Scalar.narrowAbiEligible = true := by
  cases blocks : f.blocks with
  | nil => simp [rankedLeafEligible,blocks] at checked
  | cons entry rest =>
    cases term : entry.term <;> simp only [rankedLeafEligible,blocks,term] at checked
    case brif c yes no =>
      simp only [Bool.and_eq_true] at checked
      exact ⟨checked.1.2,checked.2⟩
    all_goals cases checked

/-- The same for the leaf selector: tail blocks may also end in `trap`. -/
theorem domain_of_ranked_leaf_eligible {f : Clif.Function} (checked : rankedLeafEligible f = true)
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true) : Scalar.Domain f := by
  obtain ⟨shape⟩ := ranked_leaf_eligible_shape checked
  obtain ⟨params,returns⟩ := ranked_leaf_abi checked
  have noSret : f.sig.params.find? (·.purpose == .sret) = none := by
    apply List.find?_eq_none.mpr
    intro p member
    simp [(ranked_normal_abi params) p member]
  have ordinary : (sigRets f.sig).any (·.purpose == .sret) = false := by
    rw [sigRets,noSret]
    apply Bool.eq_false_iff.mpr
    intro any
    obtain ⟨p,member,sret⟩ := List.any_eq_true.mp any
    simpa [(ranked_normal_abi returns) p member] using sret
  exact domain_of_ranked_leaf_shape shape scope dominated abi ordinary

theorem ranked_sourceOk_sound {f : Clif.Function} (checked : rankedSourceOk f = true) : Scalar.Domain f := by
  simp only [rankedSourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨eligible,scope⟩,dominated⟩,abi⟩ := checked
  exact domain_of_ranked_leaf_eligible eligible (lowerScope_of scope) (dominated_of dominated) abi

theorem ranked_check_sound {f : Clif.Function} {vc : VCode} (checked : rankedCheck f vc = true) :
    ∃ result,Scalar.Domain f ∧ Stock.lower f = .ok result ∧ result.code = vc := by
  simp only [rankedCheck,Bool.and_eq_true] at checked
  obtain ⟨source,lowered⟩ := checked
  cases run : Stock.lower f with
  | error message => simp [run] at lowered
  | ok result =>
    simp only [run,decide_eq_true_eq] at lowered
    exact ⟨result,ranked_sourceOk_sound source,rfl,lowered⟩

end Backend.Stock.ConditionalCfg
