import FV.Backend.Lowering.StockComparisonGeneralLoopCfg
import FV.Backend.Proof.StockComparisonGeneralLoopCarry
import FV.Backend.Proof.StockComparisonComputedArgsLoopClass

/-! Source facts of the legacy loop class with all six comparison forms (#140, CB-10).

`GeneralTerms` are the terminators of the class: as `ComputedArgsTerms` (CB-9), but a `brif`
passes no block arguments. A branch condition is a wide parameter or a `ComputedArgsCondition`
(`GeneralBranch`). `GeneralTerms.args` forgets the empty arguments. The selector
`ComparisonGeneralLoopCfg.sourceLeafEligible` derives `GeneralTerms`, the entry kind, the body
families and the ABI (`source_leaf_eligible_facts`). -/

namespace Backend.Stock.Proof.ComparisonGeneralLoopCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ParameterCfg
  Backend.Stock.Proof.ComparisonComputedArgsLoopCfg
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- A branch of the class: empty arguments, and a wide parameter or a comparison in a form of
`ComputedArgsCondition` as the condition. -/
def GeneralBranch (f : Clif.Function) (b : Clif.Block) : Prop :=
  ∃ c yes no,b.term = .brif c yes no ∧ yes.args = [] ∧ no.args = [] ∧
    (ParameterCondition f c ∨ ComputedArgsCondition f c)

/-- Every block jumps, returns, branches as `GeneralBranch`, or ends in `trap`. -/
def GeneralTerms (f : Clif.Function) : Prop :=
  ∀ (bi : Nat) (b : Clif.Block),f.blocks[bi]? = some b →
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ GeneralBranch f b ∨ ∃ c,b.term = .trap c

/-- The terminators of the class are terminators of the class with block arguments. -/
theorem GeneralTerms.args {f : Clif.Function} (terms : GeneralTerms f) : ComputedArgsTerms f := by
  intro bi b found
  rcases terms bi b found with jump | ret | ⟨c,yes,no,term,_,_,condition⟩ | trap
  · exact Or.inl jump
  · exact Or.inr (Or.inl ret)
  · exact Or.inr (Or.inr (Or.inl ⟨c,yes,no,term,condition⟩))
  · exact Or.inr (Or.inr (Or.inr trap))

end Backend.Stock.Proof.ComparisonGeneralLoopCfg

namespace Backend.Stock.ComparisonGeneralLoopCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.ComparisonGeneralLoopCfg
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem control_leaf_facts {f : Clif.Function} {bi : Nat} {b : Clif.Block}
    (block : f.blocks[bi]? = some b) (checked : controlLeafEligible f bi b b.term = true) :
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ GeneralBranch f b ∨
      (∃ c,b.term = .trap c ∧ bi ≠ 0) := by
  cases term : b.term <;> rw [term] at checked
  case trap c =>
    simp only [controlLeafEligible,bne_iff_ne,ne_eq] at checked
    exact Or.inr (Or.inr (Or.inr ⟨c,rfl,checked⟩))
  case jump bc => exact Or.inl ⟨bc,rfl⟩
  case ret xs => exact Or.inr (Or.inl ⟨xs,rfl⟩)
  case brif c yes no =>
    simp only [controlLeafEligible,controlEligible,Bool.and_eq_true] at checked
    obtain ⟨⟨⟨⟨condition,yesEmpty⟩,noEmpty⟩,_⟩,_⟩ := checked
    exact Or.inr (Or.inr (Or.inl ⟨c,yes,no,term,List.isEmpty_iff.mp yesEmpty,List.isEmpty_iff.mp noEmpty,
      ComparisonComputedArgsLoopCfg.condition_sound block condition⟩))
  all_goals simp only [controlLeafEligible,controlEligible] at checked; cases checked

/-- **The selector's source facts.** The legacy six-form loop selector derives the terminators,
the entry kind, the body families and the ABI. -/
theorem source_leaf_eligible_facts {f : Clif.Function} (checked : sourceLeafEligible f = true) :
    GeneralTerms f ∧ (∀ b,f.blocks[0]? = some b → ∀ c,b.term ≠ .trap c) ∧
    (∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst) ∧
    f.sig.params.all Scalar.narrowAbiEligible = true ∧ f.sig.returns.all Scalar.narrowAbiEligible = true := by
  simp only [sourceLeafEligible,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨controls,bodies⟩,params⟩,returns⟩ := checked
  have each : ∀ (bi : Nat) (b : Clif.Block),f.blocks[bi]? = some b → controlLeafEligible f bi b b.term = true := by
    intro bi b found
    exact List.all_eq_true.mp controls (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
  refine ⟨?_,?_,?_,params,returns⟩
  · intro bi b found
    rcases control_leaf_facts found (each bi b found) with jump | ret | branch | ⟨c,trap,_⟩
    · exact Or.inl jump
    · exact Or.inr (Or.inl ret)
    · exact Or.inr (Or.inr (Or.inl branch))
    · exact Or.inr (Or.inr (Or.inr ⟨c,trap⟩))
  · intro b found c trap
    rcases control_leaf_facts found (each 0 b found) with
      ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c',yes,no,branch,_⟩ | ⟨c',trap',entry⟩
    · rw [trap] at jump; cases jump
    · rw [trap] at ret; cases ret
    · rw [trap] at branch; cases branch
    · exact entry rfl
  · intro b member stm present
    exact Scalar.maskMixedBodyEligible_sound (List.all_eq_true.mp (List.all_eq_true.mp bodies b member) stm present)

end Backend.Stock.ComparisonGeneralLoopCfg
