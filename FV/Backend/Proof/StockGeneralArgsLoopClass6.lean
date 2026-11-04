import FV.Backend.Lowering.StockGeneralLoopCfg6
import FV.Backend.Proof.StockGeneralArgsLoopClass5
import FV.Backend.Proof.StockTableLoop

/-! Source facts of the loop classes with `br_table` terminators (#140, CB-14c).

A `br_table` of the classes (`TableBranch`) has an index declared with type `i32` and fewer than
4096 table entries; its context type is `i32` (`TableBranch.index_type`). `GeneralArgsTerms` are
the terminators of the split class `GeneralArgsLoopCfg6`: those of `GeneralArgsLoopCfg5` and the
table branches with any block arguments. `GeneralTerms` are those of the legacy class
`GeneralLoopCfg6`: those of `GeneralLoopCfg5` and the table branches whose successors take no
arguments (`EmptyTableBranch`). The selectors derive the terminators, the entry kind, the body
families and the ABI (`source_leaf_eligible_facts`). -/

namespace Backend.Stock.Proof.GeneralArgsLoopCfg6
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- A `br_table` of the classes: the index is declared with type `i32`, and the table has fewer than
4096 entries. -/
def TableBranch (f : Clif.Function) (b : Clif.Block) : Prop :=
  ∃ x dc tbl,b.term = .brTable x dc tbl ∧ GeneralArgsLoopCfg5.Declared f x .i32 ∧ tbl.length < 4096

/-- A `br_table` of the legacy class: a `TableBranch` whose successors take no arguments. -/
def EmptyTableBranch (f : Clif.Function) (b : Clif.Block) : Prop :=
  ∃ x dc tbl,b.term = .brTable x dc tbl ∧ GeneralArgsLoopCfg5.Declared f x .i32 ∧ tbl.length < 4096 ∧
    ∀ bc ∈ dc :: tbl,bc.args = []

/-- Every block jumps, returns, branches as `GeneralArgsBranch` of `GeneralArgsLoopCfg5`, branches
as `TableBranch`, or ends in `trap`. -/
def GeneralArgsTerms (f : Clif.Function) : Prop :=
  ∀ (bi : Nat) (b : Clif.Block),f.blocks[bi]? = some b →
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ GeneralArgsLoopCfg5.GeneralArgsBranch f b ∨
      TableBranch f b ∨ ∃ c,b.term = .trap c

/-- Every block jumps, returns, branches as `GeneralBranch` of `GeneralArgsLoopCfg5`, branches as
`EmptyTableBranch`, or ends in `trap`. -/
def GeneralTerms (f : Clif.Function) : Prop :=
  ∀ (bi : Nat) (b : Clif.Block),f.blocks[bi]? = some b →
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ GeneralArgsLoopCfg5.GeneralBranch f b ∨
      EmptyTableBranch f b ∨ ∃ c,b.term = .trap c

/-- The terminators of the legacy class are terminators of the split class. -/
theorem GeneralTerms.args {f : Clif.Function} (terms : GeneralTerms f) : GeneralArgsTerms f := by
  intro bi b found
  rcases terms bi b found with jump | ret | ⟨c,yes,no,term,_,_,condition⟩ | ⟨x,dc,tbl,term,declared,small,_⟩ | trap
  · exact Or.inl jump
  · exact Or.inr (Or.inl ret)
  · exact Or.inr (Or.inr (Or.inl ⟨c,yes,no,term,condition⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x,dc,tbl,term,declared,small⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr trap)))

/-- The terminators of `GeneralArgsLoopCfg5` are terminators of the split class. -/
theorem general_args_terms_of_cfg5 {f : Clif.Function} (terms : GeneralArgsLoopCfg5.GeneralArgsTerms f) :
    GeneralArgsTerms f := by
  intro bi b found
  rcases terms bi b found with jump | ret | branch | trap
  · exact Or.inl jump
  · exact Or.inr (Or.inl ret)
  · exact Or.inr (Or.inr (Or.inl branch))
  · exact Or.inr (Or.inr (Or.inr (Or.inr trap)))

/-- The terminators of `GeneralLoopCfg5` are terminators of the legacy class. -/
theorem general_terms_of_cfg5 {f : Clif.Function} (terms : GeneralArgsLoopCfg5.GeneralTerms f) :
    GeneralTerms f := by
  intro bi b found
  rcases terms bi b found with jump | ret | branch | trap
  · exact Or.inl jump
  · exact Or.inr (Or.inl ret)
  · exact Or.inr (Or.inr (Or.inl branch))
  · exact Or.inr (Or.inr (Or.inr (Or.inr trap)))

/-- **The index of a table branch has the context type `i32`.** -/
theorem TableBranch.index_type {f : Clif.Function} {x : Nat}
    (declared : GeneralArgsLoopCfg5.Declared f x .i32) (scope : LowerScope f) (dominated : Dominated f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : ctx.valueType? x = some (.int 32) :=
  declared.metadata scope dominated build

end Backend.Stock.Proof.GeneralArgsLoopCfg6

namespace Backend.Stock.GeneralArgsLoopCfg6
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.GeneralArgsLoopCfg6
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The executable table check derives the declared `i32` index and the table bound. -/
theorem table_sound {f : Clif.Function} {x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    (checked : tableEligible f x dc tbl = true) :
    Proof.GeneralArgsLoopCfg5.Declared f x .i32 ∧ tbl.length < 4096 := by
  simp only [tableEligible,Bool.and_eq_true,decide_eq_true_eq] at checked
  exact ⟨GeneralArgsLoopCfg5.declared_of_sound checked.1.1,checked.1.2⟩

private theorem control_leaf_facts {f : Clif.Function} {bi : Nat} {b : Clif.Block}
    (block : f.blocks[bi]? = some b) (checked : controlLeafEligible f bi b b.term = true) :
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ Proof.GeneralArgsLoopCfg5.GeneralArgsBranch f b ∨
      TableBranch f b ∨ (∃ c,b.term = .trap c ∧ bi ≠ 0) := by
  cases term : b.term <;> rw [term] at checked
  case trap c =>
    simp only [controlLeafEligible,bne_iff_ne,ne_eq] at checked
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨c,rfl,checked⟩)))
  case jump bc => exact Or.inl ⟨bc,rfl⟩
  case ret xs => exact Or.inr (Or.inl ⟨xs,rfl⟩)
  case brif c yes no =>
    simp only [controlLeafEligible,controlEligible,GeneralArgsLoopCfg5.controlEligible,Bool.and_eq_true] at checked
    obtain ⟨⟨condition,_⟩,_⟩ := checked
    exact Or.inr (Or.inr (Or.inl ⟨c,yes,no,term,GeneralArgsLoopCfg5.condition_sound block condition⟩))
  case brTable x dc tbl =>
    simp only [controlLeafEligible,controlEligible] at checked
    obtain ⟨declared,small⟩ := table_sound checked
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x,dc,tbl,term,declared,small⟩)))
  all_goals simp only [controlLeafEligible,controlEligible,GeneralArgsLoopCfg5.controlEligible] at checked; cases checked

/-- **The split selector's source facts.** The selector derives the terminators, the entry kind,
the body families and the ABI. -/
theorem source_leaf_eligible_facts {f : Clif.Function} (checked : sourceLeafEligible f = true) :
    GeneralArgsTerms f ∧ (∀ b,f.blocks[0]? = some b → ∀ c,b.term ≠ .trap c) ∧
    (∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst) ∧
    f.sig.params.all Scalar.narrowAbiEligible = true ∧ f.sig.returns.all Scalar.narrowAbiEligible = true := by
  simp only [sourceLeafEligible,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨controls,bodies⟩,params⟩,returns⟩ := checked
  have each : ∀ (bi : Nat) (b : Clif.Block),f.blocks[bi]? = some b → controlLeafEligible f bi b b.term = true := by
    intro bi b found
    exact List.all_eq_true.mp controls (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
  refine ⟨?_,?_,?_,params,returns⟩
  · intro bi b found
    rcases control_leaf_facts found (each bi b found) with jump | ret | branch | table | ⟨c,trap,_⟩
    · exact Or.inl jump
    · exact Or.inr (Or.inl ret)
    · exact Or.inr (Or.inr (Or.inl branch))
    · exact Or.inr (Or.inr (Or.inr (Or.inl table)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨c,trap⟩)))
  · intro b found c trap
    rcases control_leaf_facts found (each 0 b found) with
      ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c',yes,no,branch,_⟩ | ⟨x,dc,tbl,table,_⟩ | ⟨c',trap',entry⟩
    · rw [trap] at jump; cases jump
    · rw [trap] at ret; cases ret
    · rw [trap] at branch; cases branch
    · rw [trap] at table; cases table
    · exact entry rfl
  · intro b member stm present
    exact Scalar.maskMixedBodyEligible_sound (List.all_eq_true.mp (List.all_eq_true.mp bodies b member) stm present)

end Backend.Stock.GeneralArgsLoopCfg6

namespace Backend.Stock.GeneralLoopCfg6
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.GeneralArgsLoopCfg6
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem control_leaf_facts {f : Clif.Function} {bi : Nat} {b : Clif.Block}
    (block : f.blocks[bi]? = some b) (checked : controlLeafEligible f bi b b.term = true) :
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ Proof.GeneralArgsLoopCfg5.GeneralBranch f b ∨
      EmptyTableBranch f b ∨ (∃ c,b.term = .trap c ∧ bi ≠ 0) := by
  cases term : b.term <;> rw [term] at checked
  case trap c =>
    simp only [controlLeafEligible,bne_iff_ne,ne_eq] at checked
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨c,rfl,checked⟩)))
  case jump bc => exact Or.inl ⟨bc,rfl⟩
  case ret xs => exact Or.inr (Or.inl ⟨xs,rfl⟩)
  case brif c yes no =>
    simp only [controlLeafEligible,controlEligible,GeneralLoopCfg5.controlEligible,Bool.and_eq_true] at checked
    obtain ⟨⟨⟨⟨condition,yesEmpty⟩,noEmpty⟩,_⟩,_⟩ := checked
    exact Or.inr (Or.inr (Or.inl ⟨c,yes,no,term,List.isEmpty_iff.mp yesEmpty,List.isEmpty_iff.mp noEmpty,
      GeneralArgsLoopCfg5.condition_sound block condition⟩))
  case brTable x dc tbl =>
    simp only [controlLeafEligible,controlEligible,Bool.and_eq_true] at checked
    obtain ⟨table,empty⟩ := checked
    obtain ⟨declared,small⟩ := GeneralArgsLoopCfg6.table_sound table
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨x,dc,tbl,term,declared,small,?_⟩)))
    intro bc member
    exact List.isEmpty_iff.mp (List.all_eq_true.mp empty bc member)
  all_goals simp only [controlLeafEligible,controlEligible,GeneralLoopCfg5.controlEligible] at checked; cases checked

/-- **The legacy selector's source facts.** The selector derives the terminators, the entry kind,
the body families and the ABI. -/
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
    rcases control_leaf_facts found (each bi b found) with jump | ret | branch | table | ⟨c,trap,_⟩
    · exact Or.inl jump
    · exact Or.inr (Or.inl ret)
    · exact Or.inr (Or.inr (Or.inl branch))
    · exact Or.inr (Or.inr (Or.inr (Or.inl table)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨c,trap⟩)))
  · intro b found c trap
    rcases control_leaf_facts found (each 0 b found) with
      ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c',yes,no,branch,_⟩ | ⟨x,dc,tbl,table,_⟩ | ⟨c',trap',entry⟩
    · rw [trap] at jump; cases jump
    · rw [trap] at ret; cases ret
    · rw [trap] at branch; cases branch
    · rw [trap] at table; cases table
    · exact entry rfl
  · intro b member stm present
    exact Scalar.maskMixedBodyEligible_sound (List.all_eq_true.mp (List.all_eq_true.mp bodies b member) stm present)

end Backend.Stock.GeneralLoopCfg6
