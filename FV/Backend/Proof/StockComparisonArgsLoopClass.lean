import FV.Backend.Lowering.StockComparisonArgsLoopCfg
import FV.Backend.Proof.StockComparisonLoopClass

/-! Source facts of the loop class with comparison branches and block arguments (#140, T7b-9).

`ArgsLoopTerms` are the terminators of the class: a `brif` may pass any block arguments, and its
condition is a wide parameter (`ParameterCondition`) or a comparison in one of the three forms
(`ComparisonCondition`, T7b-7). `condition_metadata` derives, per branching block, the built
context's metadata of the condition: the parameter metadata, or `ComparisonMetadata` by
`ComparisonCondition.metadata`. The selector `ComparisonArgsLoopCfg.sourceLeafEligible` derives
`ArgsLoopTerms`, the entry kind, the body families and the ABI (`source_leaf_eligible_facts`). -/

namespace Backend.Stock.Proof.ComparisonArgsLoopCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues Backend.Stock.Proof.ParameterCfg
  Backend.Stock.Proof.ComparisonLoopCfg
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- A branch of the class: any block arguments, and a wide parameter or a comparison as the
condition. -/
def ArgsLoopBranch (f : Clif.Function) (b : Clif.Block) : Prop :=
  ∃ c yes no,b.term = .brif c yes no ∧ (ParameterCondition f c ∨ ComparisonCondition f c)

/-- Every block jumps, returns, branches as `ArgsLoopBranch`, or ends in `trap`. -/
def ArgsLoopTerms (f : Clif.Function) : Prop :=
  ∀ (bi : Nat) (b : Clif.Block),f.blocks[bi]? = some b →
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ ArgsLoopBranch f b ∨ ∃ c,b.term = .trap c

/-- **Per-block condition metadata.** A branch condition of the class has, in the built context,
the metadata of a wide parameter or the comparison metadata of its form. -/
theorem condition_metadata {f : Clif.Function} {c : Nat}
    (condition : ParameterCondition f c ∨ ComparisonCondition f c) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) :
    (ctx.defInst? c = none ∧ (ctx.valueType? c = some (.int 32) ∨ ctx.valueType? c = some (.int 64))) ∨
      ComparisonMetadata ctx c := by
  rcases condition with parameter | comparison
  · exact Or.inl (parameter_metadata parameter dominated.ssa build)
  · exact Or.inr (comparison.metadata dominated build)

end Backend.Stock.Proof.ComparisonArgsLoopCfg

namespace Backend.Stock.ComparisonArgsLoopCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.ComparisonLoopCfg
  Backend.Stock.Proof.ComparisonArgsLoopCfg
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem control_leaf_facts {f : Clif.Function} {bi : Nat} {b : Clif.Block}
    (block : f.blocks[bi]? = some b) (checked : controlLeafEligible f bi b b.term = true) :
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ ArgsLoopBranch f b ∨
      (∃ c,b.term = .trap c ∧ bi ≠ 0) := by
  cases term : b.term <;> rw [term] at checked
  case trap c =>
    simp only [controlLeafEligible,bne_iff_ne,ne_eq] at checked
    exact Or.inr (Or.inr (Or.inr ⟨c,rfl,checked⟩))
  case jump bc => exact Or.inl ⟨bc,rfl⟩
  case ret xs => exact Or.inr (Or.inl ⟨xs,rfl⟩)
  case brif c yes no =>
    simp only [controlLeafEligible,controlEligible,Bool.and_eq_true] at checked
    obtain ⟨⟨condition,_⟩,_⟩ := checked
    exact Or.inr (Or.inr (Or.inl ⟨c,yes,no,term,ComparisonLoopCfg.condition_sound block condition⟩))
  all_goals simp only [controlLeafEligible,controlEligible] at checked; cases checked

/-- **The selector's source facts.** The selector derives the terminators, the entry kind, the
body families and the ABI. -/
theorem source_leaf_eligible_facts {f : Clif.Function} (checked : sourceLeafEligible f = true) :
    ArgsLoopTerms f ∧ (∀ b,f.blocks[0]? = some b → ∀ c,b.term ≠ .trap c) ∧
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

end Backend.Stock.ComparisonArgsLoopCfg
