import FV.Backend.Lowering.StockComparisonGeneralLoopCfg
import FV.Backend.Lowering.StockComparisonCfg
import FV.Backend.Lowering.StockConditionalRankedCfg
import FV.Backend.Lowering.StockLinearCfg
import FV.Backend.Lowering.StockTwoBlock
import FV.Backend.Lowering.StockTwoBlockEntry

/-! Subsumption of the earlier loop and branch classes by the two classes of CB-10 (#140).

The legacy class `ComparisonGeneralLoopCfg` accepts every function of the earlier legacy
(unsplit-code, empty `brif` arguments) classes: `ComparisonCfg` (CB-4), `ComparisonImmCfg` (CB-7),
`ComparisonZeroCfg` (CB-7d), `ConditionalCfg` (leaf and ranked), `ParameterCfg`, `ForwardCfg`,
`LinearCfg`, `TwoBlock`, `TwoBlock.Entry`, `ParameterLoopCfg` (T7b-5), `ComparisonLoopCfg`
(T7b-7) and `ComparisonComputedLoopCfg` (CB-8). Each of these checkers publishes the unsplit code
of the actual Stock lowering, so the subsumption also holds for the checkers.

The split class `ComparisonComputedArgsLoopCfg` (CB-9) accepts every function of the earlier
split classes `ParameterArgsCfg` (`sourceOk` and `anySourceOk`), `ParameterArgsLoopCfg` (T7b-8)
and `ComparisonArgsLoopCfg` (T7b-9), and of `ComparisonGeneralLoopCfg`. The split checkers publish
the edge split of the actual Stock lowering, so the subsumption also holds for the split checkers.

All proofs are Boolean reasoning over the `all`/`any` structure of the selectors. -/

namespace Backend.Stock.ComparisonGeneralLoopCfg
open Backend.Proof.Driver
set_option autoImplicit false

/-! ### Conditions and targets -/

/-- A forward target is a nonentry target. -/
theorem nonentry_of_after {f : Clif.Function} {bi : Nat} {bc : Clif.BlockCall}
    (after : ParameterCfg.targetAfter f bi bc = true) : ParameterLoopCfg.targetNonentry f bc = true := by
  simp only [ParameterCfg.targetAfter,ParameterLoopCfg.targetNonentry] at after ⊢
  cases found : f.blocks.findIdx? (·.id == bc.block) with
  | none => rw [found] at after; cases after
  | some target =>
    rw [found] at after
    simp only [decide_eq_true_eq] at after ⊢
    omega

/-- A `ConditionalCfg` target has no arguments and is a nonentry target. -/
theorem nonentry_of_target {f : Clif.Function} {bc : Clif.BlockCall}
    (target : ConditionalCfg.targetEligible f bc = true) :
    bc.args.isEmpty = true ∧ ParameterLoopCfg.targetNonentry f bc = true := by
  simp only [ConditionalCfg.targetEligible,Bool.and_eq_true] at target
  exact ⟨target.1,target.2⟩

/-- The comparison conditions of `ComparisonComputedLoopCfg` are conditions of
`ComparisonComputedArgsLoopCfg`. -/
theorem condition_of_computed {f : Clif.Function} {b : Clif.Block} {c : Nat}
    (computed : ComparisonComputedLoopCfg.conditionEligible f b c = true) :
    ComparisonComputedArgsLoopCfg.conditionEligible f b c = true := by
  simp only [ComparisonComputedArgsLoopCfg.conditionEligible,computed,Bool.true_or]

/-- The conditions of `ComparisonLoopCfg` are conditions of `ComparisonComputedLoopCfg`. -/
theorem computed_of_loop {f : Clif.Function} {b : Clif.Block} {c : Nat}
    (loop : ComparisonLoopCfg.conditionEligible f b c = true) :
    ComparisonComputedLoopCfg.conditionEligible f b c = true := by
  simp only [ComparisonLoopCfg.conditionEligible,ComparisonComputedLoopCfg.conditionEligible,Bool.or_eq_true,
    List.any_eq_true] at loop ⊢
  rcases loop with parameter | ⟨stm,member,comparison⟩
  · exact Or.inl parameter
  · exact Or.inr ⟨stm,member,by simp only [ComparisonComputedLoopCfg.comparisonEligible,comparison,Bool.true_or]⟩

/-- A wide-parameter condition is a condition of `ComparisonLoopCfg`. -/
theorem loop_of_parameter {f : Clif.Function} {b : Clif.Block} {c : Nat}
    (parameter : ParameterCfg.parameterEligible f c = true) : ComparisonLoopCfg.conditionEligible f b c = true := by
  simp only [ComparisonLoopCfg.conditionEligible,parameter,Bool.true_or]

/-- A condition of `ComparisonLoopCfg` is a condition of `ComparisonComputedArgsLoopCfg`. -/
theorem condition_of_loop {f : Clif.Function} {b : Clif.Block} {c : Nat}
    (loop : ComparisonLoopCfg.conditionEligible f b c = true) :
    ComparisonComputedArgsLoopCfg.conditionEligible f b c = true :=
  condition_of_computed (computed_of_loop loop)

/-- A wide-parameter condition is a condition of `ComparisonComputedArgsLoopCfg`. -/
theorem condition_of_parameter {f : Clif.Function} {b : Clif.Block} {c : Nat}
    (parameter : ParameterCfg.parameterEligible f c = true) :
    ComparisonComputedArgsLoopCfg.conditionEligible f b c = true :=
  condition_of_loop (loop_of_parameter parameter)

/-- A wide entry parameter is a wide parameter of some block. -/
theorem parameter_of_entry {f : Clif.Function} {entry : Clif.Block} (member : entry ∈ f.blocks) {c : Nat}
    (parameter : entry.params.any (fun (value,ty) => value == c && (ty == .i32 || ty == .i64)) = true) :
    ParameterCfg.parameterEligible f c = true :=
  List.any_eq_true.mpr ⟨entry,member,parameter⟩

private theorem parameter_of {f : Clif.Function} {entry : Clif.Block} (member : entry ∈ f.blocks)
    {x : Nat} {ty : Clif.Ty} (present : entry.params.contains (x,ty) = true) :
    ComparisonLoopCfg.parameterOf f x ty = true :=
  List.any_eq_true.mpr ⟨entry,member,present⟩

private theorem statement_of {f : Clif.Function} {entry : Clif.Block} (member : entry ∈ f.blocks)
    {eligible : Clif.Stmt → Bool} (present : entry.body.any eligible = true) :
    ComparisonLoopCfg.statementOf f eligible = true :=
  List.any_eq_true.mpr ⟨entry,member,present⟩

/-- An entry comparison of two entry parameters (`ComparisonCfg`) is a comparison of
`ComparisonLoopCfg`. -/
theorem comparison_of_entry {f : Clif.Function} {entry : Clif.Block} (member : entry ∈ f.blocks)
    {c : Nat} {stm : Clif.Stmt} (checked : ComparisonCfg.comparisonEligible entry c stm = true) :
    ComparisonLoopCfg.comparisonEligible f c stm = true := by
  obtain ⟨results,inst⟩ := stm
  simp only [ComparisonCfg.comparisonEligible,ComparisonLoopCfg.comparisonEligible,Bool.and_eq_true] at checked ⊢
  refine ⟨checked.1,?_⟩
  have operands := checked.2
  cases inst <;> simp only [Bool.false_eq_true] at operands ⊢
  case icmp cc ty x y =>
    simp only [Bool.or_eq_true,Bool.and_eq_true] at operands ⊢
    rcases operands with ⟨narrowX,narrowY⟩ | ⟨wideX,wideY⟩
    · exact Or.inl (Or.inl ⟨parameter_of member narrowX,parameter_of member narrowY⟩)
    · exact Or.inl (Or.inr ⟨parameter_of member wideX,parameter_of member wideY⟩)

/-- An entry comparison of an entry parameter with a 12-bit immediate (`ComparisonImmCfg`) is a
comparison of `ComparisonLoopCfg`. -/
theorem comparison_of_entry_imm {f : Clif.Function} {entry : Clif.Block} (member : entry ∈ f.blocks)
    {c : Nat} {stm : Clif.Stmt} (checked : ComparisonImmCfg.immEligible entry c stm = true) :
    ComparisonLoopCfg.comparisonEligible f c stm = true := by
  obtain ⟨results,inst⟩ := stm
  simp only [ComparisonImmCfg.immEligible,ComparisonLoopCfg.comparisonEligible,Bool.and_eq_true] at checked ⊢
  refine ⟨checked.1,?_⟩
  have operands := checked.2
  cases inst <;> simp only [Bool.false_eq_true] at operands ⊢
  case icmp cc ty x y =>
    simp only [Bool.or_eq_true,Bool.and_eq_true] at operands ⊢
    obtain ⟨first,constant⟩ := operands
    refine Or.inr ⟨?_,Or.inl (statement_of member constant)⟩
    rcases first with narrowX | wideX
    · exact Or.inl (parameter_of member narrowX)
    · exact Or.inr (parameter_of member wideX)

/-- An entry `eq`/`ne` comparison of an entry parameter with zero (`ComparisonZeroCfg`) is a
comparison of `ComparisonLoopCfg`. -/
theorem comparison_of_entry_zero {f : Clif.Function} {entry : Clif.Block} (member : entry ∈ f.blocks)
    {c : Nat} {stm : Clif.Stmt} (checked : ComparisonZeroCfg.zeroEligible entry c stm = true) :
    ComparisonLoopCfg.comparisonEligible f c stm = true := by
  obtain ⟨results,inst⟩ := stm
  simp only [ComparisonZeroCfg.zeroEligible,ComparisonLoopCfg.comparisonEligible,Bool.and_eq_true] at checked ⊢
  refine ⟨checked.1,?_⟩
  have operands := checked.2
  cases inst <;> simp only [Bool.false_eq_true] at operands ⊢
  case icmp cc ty x y =>
    simp only [Bool.or_eq_true,Bool.and_eq_true] at operands ⊢
    obtain ⟨⟨equality,first⟩,constant⟩ := operands
    refine Or.inr ⟨?_,Or.inr ⟨equality,statement_of member constant⟩⟩
    rcases first with narrowX | wideX
    · exact Or.inl (parameter_of member narrowX)
    · exact Or.inr (parameter_of member wideX)

/-- An entry `brif` condition that a comparison of `ComparisonLoopCfg` in the entry body defines
is a condition of `ComparisonComputedArgsLoopCfg`. -/
theorem condition_of_entry_body {f : Clif.Function} {entry : Clif.Block} {c : Nat}
    {eligible : Clif.Stmt → Bool}
    (lift : ∀ stm,eligible stm = true → ComparisonLoopCfg.comparisonEligible f c stm = true)
    (present : entry.body.any eligible = true) :
    ComparisonComputedArgsLoopCfg.conditionEligible f entry c = true := by
  obtain ⟨stm,statement,good⟩ := List.any_eq_true.mp present
  apply condition_of_loop
  simp only [ComparisonLoopCfg.conditionEligible,Bool.or_eq_true]
  exact Or.inr (List.any_eq_true.mpr ⟨stm,statement,lift stm good⟩)

/-! ### Selector structure -/

/-- `sourceLeafEligible` from the control check of every block, the bodies and the ABI. -/
theorem source_leaf_eligible_of_blocks {f : Clif.Function}
    (controls : ∀ (bi : Nat) (b : Clif.Block),f.blocks[bi]? = some b → controlLeafEligible f bi b b.term = true)
    (bodies : f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) = true)
    (params : f.sig.params.all Scalar.narrowAbiEligible = true)
    (returns : f.sig.returns.all Scalar.narrowAbiEligible = true) : sourceLeafEligible f = true := by
  simp only [sourceLeafEligible,Bool.and_eq_true]
  refine ⟨⟨⟨?_,bodies⟩,params⟩,returns⟩
  apply List.all_eq_true.mpr
  rintro ⟨b,bi⟩ member
  exact controls bi b (List.mk_mem_zipIdx_iff_getElem?.mp member)

/-- `sourceOk` from `sourceLeafEligible` and the driver checks. -/
theorem source_ok_of_leaf {f : Clif.Function} (leaf : sourceLeafEligible f = true) (scope : lowerScopeB f = true)
    (dominated : dominatedB f = true) (abi : sigAbiOk f.sig = true) : sourceOk f = true := by
  simp only [sourceOk,leaf,scope,dominated,abi,Bool.and_self]

/-- `sourceLeafEligible` of a function whose entry block is `entry`, from the control checks of
`entry` and of the other blocks. -/
theorem source_leaf_eligible_of_entry {f : Clif.Function} {entry : Clif.Block} {rest : List Clif.Block}
    (blocks : f.blocks = entry :: rest)
    (entryOk : controlLeafEligible f 0 entry entry.term = true)
    (restOk : ∀ (bi : Nat) (b : Clif.Block),rest[bi]? = some b → controlLeafEligible f (bi+1) b b.term = true)
    (bodies : f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) = true)
    (params : f.sig.params.all Scalar.narrowAbiEligible = true)
    (returns : f.sig.returns.all Scalar.narrowAbiEligible = true) : sourceLeafEligible f = true := by
  refine source_leaf_eligible_of_blocks ?_ bodies params returns
  intro bi b found
  rw [blocks] at found
  cases bi with
  | zero =>
    simp only [List.getElem?_cons_zero,Option.some.injEq] at found
    subst found
    exact entryOk
  | succ bi =>
    simp only [List.getElem?_cons_succ] at found
    exact restOk bi b found

/-- A nonentry block that returns or ends in `trap` passes the control check. -/
theorem control_of_leaf {f : Clif.Function} {bi : Nat} {b : Clif.Block}
    (leaf : (match b.term with | .ret _ | .trap _ => true | _ => false) = true) :
    controlLeafEligible f (bi+1) b b.term = true := by
  cases term : b.term <;> simp only [term] at leaf <;>
    simp only [controlLeafEligible,controlEligible,bne_iff_ne,ne_eq,Nat.add_one_ne_zero,not_false_eq_true] <;>
    cases leaf

/-- A `brif` of the entry block on an eligible condition into `ConditionalCfg` targets passes the
control check. -/
theorem control_of_entry_branch {f : Clif.Function} {entry : Clif.Block} {c : Nat} {yes no : Clif.BlockCall}
    (term : entry.term = .brif c yes no)
    (condition : ComparisonComputedArgsLoopCfg.conditionEligible f entry c = true)
    (yesOk : ConditionalCfg.targetEligible f yes = true) (noOk : ConditionalCfg.targetEligible f no = true) :
    controlLeafEligible f 0 entry entry.term = true := by
  obtain ⟨yesEmpty,yesNonentry⟩ := nonentry_of_target yesOk
  obtain ⟨noEmpty,noNonentry⟩ := nonentry_of_target noOk
  simp only [term,controlLeafEligible,controlEligible,condition,yesEmpty,noEmpty,yesNonentry,noNonentry,
    Bool.and_self]

/-- The nonentry blocks of the forward branch classes (`ComparisonCfg`, `ConditionalCfg`): every
block returns or ends in `trap`. -/
theorem rest_of_leaves {f : Clif.Function} {rest : List Clif.Block}
    (leaves : rest.all (fun b => b.params.isEmpty && match b.term with | .ret _ | .trap _ => true | _ => false) = true) :
    ∀ (bi : Nat) (b : Clif.Block),rest[bi]? = some b → controlLeafEligible f (bi+1) b b.term = true := by
  intro bi b found
  have good := List.all_eq_true.mp leaves b (List.mem_of_getElem? found)
  simp only [Bool.and_eq_true] at good
  exact control_of_leaf good.2

/-! ### Legacy subsumption -/

/-- **`ComparisonCfg` (CB-4) is in the class at the selector level.** -/
theorem source_leaf_eligible_of_comparison {f : Clif.Function}
    (leaf : ComparisonCfg.leafEligible f = true) : sourceLeafEligible f = true := by
  unfold ComparisonCfg.leafEligible at leaf
  cases blocks : f.blocks with
  | nil => rw [blocks] at leaf; cases leaf
  | cons entry rest =>
    rw [blocks] at leaf
    dsimp only at leaf
    cases term : entry.term <;> rw [term] at leaf <;> try cases leaf
    case brif c yes no =>
      simp only [Bool.and_eq_true] at leaf
      obtain ⟨⟨⟨⟨⟨⟨condition,yesOk⟩,noOk⟩,leaves⟩,bodies⟩,params⟩,returns⟩ := leaf
      rw [← blocks] at bodies
      have member : entry ∈ f.blocks := by rw [blocks]; exact List.mem_cons_self
      exact source_leaf_eligible_of_entry blocks
        (control_of_entry_branch term (condition_of_entry_body (fun _ => comparison_of_entry member) condition)
          yesOk noOk)
        (rest_of_leaves leaves) bodies params returns

/-- **`ComparisonCfg` (CB-4) is in the class.** -/
theorem source_ok_of_comparison {f : Clif.Function} (checked : ComparisonCfg.sourceOk f = true) :
    sourceOk f = true := by
  simp only [ComparisonCfg.sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨leaf,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_comparison leaf) scope dominated abi

/-- **`ComparisonImmCfg` (CB-7) is in the class at the selector level.** -/
theorem source_leaf_eligible_of_comparison_imm {f : Clif.Function}
    (leaf : ComparisonImmCfg.leafEligible f = true) : sourceLeafEligible f = true := by
  unfold ComparisonImmCfg.leafEligible at leaf
  cases blocks : f.blocks with
  | nil => rw [blocks] at leaf; cases leaf
  | cons entry rest =>
    rw [blocks] at leaf
    dsimp only at leaf
    cases term : entry.term <;> rw [term] at leaf <;> try cases leaf
    case brif c yes no =>
      simp only [Bool.and_eq_true] at leaf
      obtain ⟨⟨⟨⟨⟨⟨condition,yesOk⟩,noOk⟩,leaves⟩,bodies⟩,params⟩,returns⟩ := leaf
      rw [← blocks] at bodies
      have member : entry ∈ f.blocks := by rw [blocks]; exact List.mem_cons_self
      exact source_leaf_eligible_of_entry blocks
        (control_of_entry_branch term (condition_of_entry_body (fun _ => comparison_of_entry_imm member) condition)
          yesOk noOk)
        (rest_of_leaves leaves) bodies params returns

/-- **`ComparisonImmCfg` (CB-7) is in the class.** -/
theorem source_ok_of_comparison_imm {f : Clif.Function} (checked : ComparisonImmCfg.sourceOk f = true) :
    sourceOk f = true := by
  simp only [ComparisonImmCfg.sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨leaf,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_comparison_imm leaf) scope dominated abi

/-- **`ComparisonZeroCfg` (CB-7d) is in the class at the selector level.** -/
theorem source_leaf_eligible_of_comparison_zero {f : Clif.Function}
    (leaf : ComparisonZeroCfg.leafEligible f = true) : sourceLeafEligible f = true := by
  unfold ComparisonZeroCfg.leafEligible at leaf
  cases blocks : f.blocks with
  | nil => rw [blocks] at leaf; cases leaf
  | cons entry rest =>
    rw [blocks] at leaf
    dsimp only at leaf
    cases term : entry.term <;> rw [term] at leaf <;> try cases leaf
    case brif c yes no =>
      simp only [Bool.and_eq_true] at leaf
      obtain ⟨⟨⟨⟨⟨⟨condition,yesOk⟩,noOk⟩,leaves⟩,bodies⟩,params⟩,returns⟩ := leaf
      rw [← blocks] at bodies
      have member : entry ∈ f.blocks := by rw [blocks]; exact List.mem_cons_self
      exact source_leaf_eligible_of_entry blocks
        (control_of_entry_branch term (condition_of_entry_body (fun _ => comparison_of_entry_zero member) condition)
          yesOk noOk)
        (rest_of_leaves leaves) bodies params returns

/-- **`ComparisonZeroCfg` (CB-7d) is in the class.** -/
theorem source_ok_of_comparison_zero {f : Clif.Function} (checked : ComparisonZeroCfg.sourceOk f = true) :
    sourceOk f = true := by
  simp only [ComparisonZeroCfg.sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨leaf,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_comparison_zero leaf) scope dominated abi

/-- **`ConditionalCfg` (wide entry-parameter branches into return or trap blocks) is in the
class.** -/
theorem source_leaf_eligible_of_conditional {f : Clif.Function}
    (leaf : ConditionalCfg.leafEligible f = true) : sourceLeafEligible f = true := by
  unfold ConditionalCfg.leafEligible at leaf
  cases blocks : f.blocks with
  | nil => rw [blocks] at leaf; cases leaf
  | cons entry rest =>
    rw [blocks] at leaf
    dsimp only at leaf
    cases term : entry.term <;> rw [term] at leaf <;> try cases leaf
    case brif c yes no =>
      simp only [Bool.and_eq_true] at leaf
      obtain ⟨⟨⟨⟨⟨⟨condition,yesOk⟩,noOk⟩,leaves⟩,bodies⟩,params⟩,returns⟩ := leaf
      rw [← blocks] at bodies
      have member : entry ∈ f.blocks := by rw [blocks]; exact List.mem_cons_self
      exact source_leaf_eligible_of_entry blocks
        (control_of_entry_branch term (condition_of_parameter (parameter_of_entry member condition)) yesOk noOk)
        (rest_of_leaves leaves) bodies params returns

/-- **`ConditionalCfg` (wide entry-parameter branches into return or trap blocks) is in the
class.** -/
theorem source_ok_of_conditional {f : Clif.Function} (checked : ConditionalCfg.sourceOk f = true) :
    sourceOk f = true := by
  simp only [ConditionalCfg.sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨leaf,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_conditional leaf) scope dominated abi

/-- A `ForwardCfg` control check of a block that does not end in `trap` at the entry index is a
control check of the class. -/
theorem control_of_forward {f : Clif.Function} {bi : Nat} {b : Clif.Block}
    (forward : ForwardCfg.controlLeafEligible f bi b.term = true)
    (entryKind : bi = 0 → ∀ c,b.term ≠ .trap c) : controlLeafEligible f bi b b.term = true := by
  cases term : b.term <;> rw [term] at forward
  case trap c =>
    have nonzero : bi ≠ 0 := fun zero => entryKind zero c term
    simp only [controlLeafEligible,bne_iff_ne,ne_eq,nonzero,not_false_eq_true]
  case jump bc =>
    simp only [controlLeafEligible,controlEligible]
    exact nonentry_of_after forward
  case ret xs => simp only [controlLeafEligible,controlEligible]
  all_goals simp only [ForwardCfg.controlLeafEligible,ForwardCfg.controlEligible] at forward; cases forward

/-- **`ConditionalCfg.rankedSourceOk` (ranked forward tails after a wide entry-parameter
branch) is in the class at the selector level.** -/
theorem source_leaf_eligible_of_conditional_ranked {f : Clif.Function}
    (leaf : ConditionalCfg.rankedLeafEligible f = true) : sourceLeafEligible f = true := by
  unfold ConditionalCfg.rankedLeafEligible at leaf
  cases blocks : f.blocks with
  | nil => rw [blocks] at leaf; cases leaf
  | cons entry rest =>
    rw [blocks] at leaf
    dsimp only at leaf
    cases term : entry.term <;> rw [term] at leaf <;> try cases leaf
    case brif c yes no =>
      simp only [Bool.and_eq_true] at leaf
      obtain ⟨⟨⟨⟨⟨⟨condition,yesOk⟩,noOk⟩,tails⟩,bodies⟩,params⟩,returns⟩ := leaf
      rw [← blocks] at bodies
      have member : entry ∈ f.blocks := by rw [blocks]; exact List.mem_cons_self
      refine source_leaf_eligible_of_entry blocks
        (control_of_entry_branch term (condition_of_parameter (parameter_of_entry member condition)) yesOk noOk)
        ?_ bodies params returns
      intro bi b found
      have forward := List.all_eq_true.mp tails (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
      exact control_of_forward forward (fun zero => absurd zero (Nat.add_one_ne_zero bi))

/-- **`ConditionalCfg.rankedSourceOk` (ranked forward tails after a wide entry-parameter
branch) is in the class.** -/
theorem source_ok_of_conditional_ranked {f : Clif.Function} (checked : ConditionalCfg.rankedSourceOk f = true) :
    sourceOk f = true := by
  simp only [ConditionalCfg.rankedSourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨leaf,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_conditional_ranked leaf) scope dominated abi

/-- **`ForwardCfg` (ranked jump/return/trap graphs with a jumping entry) is in the class at the selector level.** -/
theorem source_leaf_eligible_of_forward {f : Clif.Function}
    (leaf : ForwardCfg.leafEligible f = true) : sourceLeafEligible f = true := by
  unfold ForwardCfg.leafEligible at leaf
  cases blocks : f.blocks with
  | nil => rw [blocks] at leaf; cases leaf
  | cons entry rest =>
    rw [blocks] at leaf
    dsimp only at leaf
    cases term : entry.term <;> rw [term] at leaf <;> try cases leaf
    case jump bc =>
      simp only [Bool.and_eq_true] at leaf
      obtain ⟨⟨⟨controls,bodies⟩,params⟩,returns⟩ := leaf
      rw [← blocks] at controls bodies
      refine source_leaf_eligible_of_blocks ?_ bodies params returns
      intro bi b found
      have forward := List.all_eq_true.mp controls (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
      refine control_of_forward forward ?_
      intro zero c trap
      subst zero
      rw [blocks] at found
      simp only [List.getElem?_cons_zero,Option.some.injEq] at found
      subst found
      rw [term] at trap
      cases trap

/-- **`ForwardCfg` (ranked jump/return/trap graphs with a jumping entry) is in the class.** -/
theorem source_ok_of_forward {f : Clif.Function} (checked : ForwardCfg.sourceOk f = true) :
    sourceOk f = true := by
  simp only [ForwardCfg.sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨leaf,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_forward leaf) scope dominated abi

/-- **`ParameterCfg` (ranked forward graphs with wide-parameter branches) is in the class at the selector level.** -/
theorem source_leaf_eligible_of_parameter {f : Clif.Function}
    (checked : ParameterCfg.sourceLeafEligible f = true) : sourceLeafEligible f = true := by
  simp only [ParameterCfg.sourceLeafEligible,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨controls,bodies⟩,params⟩,returns⟩ := checked
  refine source_leaf_eligible_of_blocks ?_ bodies params returns
  intro bi b found
  have old := List.all_eq_true.mp controls (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
  cases term : b.term <;> rw [term] at old
  case trap c => exact old
  case jump bc => exact nonentry_of_after old
  case ret xs => rfl
  case brif c yes no =>
    simp only [ParameterCfg.controlLeafEligible,ParameterCfg.controlEligible,Bool.and_eq_true] at old
    obtain ⟨⟨⟨⟨condition,yesEmpty⟩,noEmpty⟩,yesAfter⟩,noAfter⟩ := old
    simp only [controlLeafEligible,controlEligible,condition_of_parameter condition,yesEmpty,noEmpty,
      nonentry_of_after yesAfter,nonentry_of_after noAfter,Bool.and_self]
  all_goals simp only [ParameterCfg.controlLeafEligible,ParameterCfg.controlEligible] at old; cases old

/-- **`ParameterCfg` (ranked forward graphs with wide-parameter branches) is in the class.** -/
theorem source_ok_of_parameter {f : Clif.Function} (checked : ParameterCfg.sourceOk f = true) :
    sourceOk f = true := by
  simp only [ParameterCfg.sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨leaf,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_parameter leaf) scope dominated abi

/-- **`ParameterLoopCfg` (T7b-5) is in the class at the selector level.** -/
theorem source_leaf_eligible_of_parameter_loop {f : Clif.Function}
    (checked : ParameterLoopCfg.sourceLeafEligible f = true) : sourceLeafEligible f = true := by
  simp only [ParameterLoopCfg.sourceLeafEligible,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨controls,bodies⟩,params⟩,returns⟩ := checked
  refine source_leaf_eligible_of_blocks ?_ bodies params returns
  intro bi b found
  have old := List.all_eq_true.mp controls (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
  cases term : b.term <;> rw [term] at old
  case trap c => exact old
  case jump bc => exact old
  case ret xs => rfl
  case brif c yes no =>
    simp only [ParameterLoopCfg.controlLeafEligible,ParameterLoopCfg.controlEligible,Bool.and_eq_true] at old
    obtain ⟨⟨⟨⟨condition,yesEmpty⟩,noEmpty⟩,yesNonentry⟩,noNonentry⟩ := old
    simp only [controlLeafEligible,controlEligible,condition_of_parameter condition,yesEmpty,noEmpty,
      yesNonentry,noNonentry,Bool.and_self]
  all_goals simp only [ParameterLoopCfg.controlLeafEligible,ParameterLoopCfg.controlEligible] at old; cases old

/-- **`ParameterLoopCfg` (T7b-5) is in the class.** -/
theorem source_ok_of_parameter_loop {f : Clif.Function} (checked : ParameterLoopCfg.sourceOk f = true) :
    sourceOk f = true := by
  simp only [ParameterLoopCfg.sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨leaf,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_parameter_loop leaf) scope dominated abi

/-- **`ComparisonLoopCfg` (T7b-7) is in the class at the selector level.** -/
theorem source_leaf_eligible_of_comparison_loop {f : Clif.Function}
    (checked : ComparisonLoopCfg.sourceLeafEligible f = true) : sourceLeafEligible f = true := by
  simp only [ComparisonLoopCfg.sourceLeafEligible,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨controls,bodies⟩,params⟩,returns⟩ := checked
  refine source_leaf_eligible_of_blocks ?_ bodies params returns
  intro bi b found
  have old := List.all_eq_true.mp controls (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
  cases term : b.term <;> rw [term] at old
  case trap c => exact old
  case jump bc => exact old
  case ret xs => rfl
  case brif c yes no =>
    simp only [ComparisonLoopCfg.controlLeafEligible,ComparisonLoopCfg.controlEligible,Bool.and_eq_true] at old
    obtain ⟨⟨⟨⟨condition,yesEmpty⟩,noEmpty⟩,yesNonentry⟩,noNonentry⟩ := old
    simp only [controlLeafEligible,controlEligible,condition_of_loop condition,yesEmpty,noEmpty,
      yesNonentry,noNonentry,Bool.and_self]
  all_goals simp only [ComparisonLoopCfg.controlLeafEligible,ComparisonLoopCfg.controlEligible] at old; cases old

/-- **`ComparisonLoopCfg` (T7b-7) is in the class.** -/
theorem source_ok_of_comparison_loop {f : Clif.Function} (checked : ComparisonLoopCfg.sourceOk f = true) :
    sourceOk f = true := by
  simp only [ComparisonLoopCfg.sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨leaf,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_comparison_loop leaf) scope dominated abi

/-- **`ComparisonComputedLoopCfg` (CB-8) is in the class at the selector level.** -/
theorem source_leaf_eligible_of_comparison_computed_loop {f : Clif.Function}
    (checked : ComparisonComputedLoopCfg.sourceLeafEligible f = true) : sourceLeafEligible f = true := by
  simp only [ComparisonComputedLoopCfg.sourceLeafEligible,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨controls,bodies⟩,params⟩,returns⟩ := checked
  refine source_leaf_eligible_of_blocks ?_ bodies params returns
  intro bi b found
  have old := List.all_eq_true.mp controls (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
  cases term : b.term <;> rw [term] at old
  case trap c => exact old
  case jump bc => exact old
  case ret xs => rfl
  case brif c yes no =>
    simp only [ComparisonComputedLoopCfg.controlLeafEligible,ComparisonComputedLoopCfg.controlEligible,
      Bool.and_eq_true] at old
    obtain ⟨⟨⟨⟨condition,yesEmpty⟩,noEmpty⟩,yesNonentry⟩,noNonentry⟩ := old
    simp only [controlLeafEligible,controlEligible,condition_of_computed condition,yesEmpty,noEmpty,
      yesNonentry,noNonentry,Bool.and_self]
  all_goals
    simp only [ComparisonComputedLoopCfg.controlLeafEligible,ComparisonComputedLoopCfg.controlEligible] at old
    cases old

/-- **`ComparisonComputedLoopCfg` (CB-8) is in the class.** -/
theorem source_ok_of_comparison_computed_loop {f : Clif.Function} (checked : ComparisonComputedLoopCfg.sourceOk f = true) :
    sourceOk f = true := by
  simp only [ComparisonComputedLoopCfg.sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨leaf,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_comparison_computed_loop leaf) scope dominated abi

/-- The first index of a block id in a list whose head has another id is a nonzero index. -/
private theorem nonentry_of_tail {f : Clif.Function} {entry : Clif.Block} {rest : List Clif.Block}
    (blocks : f.blocks = entry :: rest) {bc : Clif.BlockCall} (other : entry.id ≠ bc.block)
    (present : (rest.findIdx? (·.id == bc.block)).isSome = true) : ParameterLoopCfg.targetNonentry f bc = true := by
  obtain ⟨i,found⟩ := Option.isSome_iff_exists.mp present
  have head : (entry.id == bc.block) = false := beq_false_of_ne other
  simp only [ParameterLoopCfg.targetNonentry,blocks,List.findIdx?_cons,head,Bool.false_eq_true,ite_false,
    found,Option.map_some]
  simp only [decide_eq_true_eq]
  omega

/-- **`LinearCfg` (three-block jump chains) is in the class at the selector level.** -/
theorem source_leaf_eligible_of_linear {f : Clif.Function}
    (eligible : LinearCfg.eligible f = true) : sourceLeafEligible f = true := by
  unfold LinearCfg.eligible at eligible
  match blocks : f.blocks,eligible with
  | [entry,middle,target],eligible =>
    dsimp only at eligible
    cases entryTerm : entry.term <;> rw [entryTerm] at eligible <;> try cases eligible
    case jump first =>
    cases middleTerm : middle.term <;> rw [middleTerm] at eligible <;> try cases eligible
    case jump second =>
    cases targetTerm : target.term <;> rw [targetTerm] at eligible <;> try cases eligible
    case ret xs =>
    simp only [Bool.and_eq_true,beq_iff_eq,bne_iff_ne,ne_eq] at eligible
    obtain ⟨⟨⟨⟨⟨⟨⟨firstTarget,secondTarget⟩,entryMiddle⟩,entryTarget⟩,middleTarget⟩,bodies⟩,params⟩,returns⟩ :=
      eligible
    refine source_leaf_eligible_of_entry blocks ?_ ?_ (by rw [blocks]; exact bodies) params returns
    · simp only [entryTerm,controlLeafEligible,controlEligible]
      exact nonentry_of_tail blocks (by rw [firstTarget]; exact entryMiddle)
        (by simp [List.findIdx?_cons,firstTarget])
    · intro bi b found
      match bi,found with
      | 0,found =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at found
        subst found
        simp only [middleTerm,controlLeafEligible,controlEligible]
        exact nonentry_of_tail blocks (by rw [secondTarget]; exact entryTarget)
          (by simp [List.findIdx?_cons,secondTarget,middleTarget])
      | 1,found =>
        simp only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at found
        subst found
        simp only [targetTerm,controlLeafEligible,controlEligible]
      | _+2,found => simp at found

/-- **`LinearCfg` (three-block jump chains) is in the class.** -/
theorem source_ok_of_linear {f : Clif.Function} (checked : LinearCfg.sourceOk f = true) :
    sourceOk f = true := by
  simp only [LinearCfg.sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨eligible,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_linear eligible) scope dominated abi

/-- **`TwoBlock` (an entry jump into a returning block) is in the class at the selector level.** -/
theorem source_leaf_eligible_of_two_block {f : Clif.Function}
    (eligible : TwoBlock.eligible f = true) : sourceLeafEligible f = true := by
  unfold TwoBlock.eligible at eligible
  match blocks : f.blocks,eligible with
  | [entry,target],eligible =>
    dsimp only at eligible
    cases entryTerm : entry.term <;> rw [entryTerm] at eligible <;> try cases eligible
    case jump bc =>
    cases targetTerm : target.term <;> rw [targetTerm] at eligible <;> try cases eligible
    case ret xs =>
    simp only [Bool.and_eq_true,beq_iff_eq,bne_iff_ne,ne_eq] at eligible
    obtain ⟨⟨⟨⟨⟨⟨jumpTarget,distinct⟩,entryBody⟩,targetBody⟩,_⟩,params⟩,returns⟩ := eligible
    have bodies : f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) = true := by
      rw [blocks]
      simp only [List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true]
      refine ⟨List.all_eq_true.mpr fun stm member => ?_,targetBody⟩
      have good := List.all_eq_true.mp entryBody stm member
      simp only [TwoBlock.entryEligible,Bool.and_eq_true] at good
      exact good.1
    refine source_leaf_eligible_of_entry blocks ?_ ?_ bodies params returns
    · simp only [entryTerm,controlLeafEligible,controlEligible]
      exact nonentry_of_tail blocks (by rw [jumpTarget]; exact distinct) (by simp [List.findIdx?_cons,jumpTarget])
    · intro bi b found
      match bi,found with
      | 0,found =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at found
        subst found
        simp only [targetTerm,controlLeafEligible,controlEligible]
      | _+1,found => simp at found

/-- **`TwoBlock` (an entry jump into a returning block) is in the class.** -/
theorem source_ok_of_two_block {f : Clif.Function} (checked : TwoBlock.sourceOk f = true) :
    sourceOk f = true := by
  simp only [TwoBlock.sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨eligible,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_two_block eligible) scope dominated abi

/-- **`TwoBlock.Entry` (an entry jump with any scalar entry body into a returning block) is in
the class at the selector level.** -/
theorem source_leaf_eligible_of_two_block_entry {f : Clif.Function}
    (eligible : TwoBlock.Entry.eligible f = true) : sourceLeafEligible f = true := by
  unfold TwoBlock.Entry.eligible at eligible
  match blocks : f.blocks,eligible with
  | [entry,target],eligible =>
    dsimp only at eligible
    cases entryTerm : entry.term <;> rw [entryTerm] at eligible <;> try cases eligible
    case jump bc =>
    cases targetTerm : target.term <;> rw [targetTerm] at eligible <;> try cases eligible
    case ret xs =>
    simp only [Bool.and_eq_true,beq_iff_eq,bne_iff_ne,ne_eq] at eligible
    obtain ⟨⟨⟨⟨⟨⟨jumpTarget,distinct⟩,entryBody⟩,targetBody⟩,_⟩,params⟩,returns⟩ := eligible
    have bodies : f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) = true := by
      rw [blocks]
      simp only [List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true]
      exact ⟨entryBody,targetBody⟩
    refine source_leaf_eligible_of_entry blocks ?_ ?_ bodies params returns
    · simp only [entryTerm,controlLeafEligible,controlEligible]
      exact nonentry_of_tail blocks (by rw [jumpTarget]; exact distinct) (by simp [List.findIdx?_cons,jumpTarget])
    · intro bi b found
      match bi,found with
      | 0,found =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at found
        subst found
        simp only [targetTerm,controlLeafEligible,controlEligible]
      | _+1,found => simp at found

/-- **`TwoBlock.Entry` (an entry jump with any scalar entry body into a returning block) is in
the class.** -/
theorem source_ok_of_two_block_entry {f : Clif.Function} (checked : TwoBlock.Entry.sourceOk f = true) :
    sourceOk f = true := by
  simp only [TwoBlock.Entry.sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨eligible,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_two_block_entry eligible) scope dominated abi

/-! ### Legacy checkers

Each legacy checker is `sourceOk f` and the equality of the unsplit actual Stock code with the
published code, so `check` accepts it whenever `sourceOk` does. -/

private theorem check_of_source {f : Clif.Function} {vc : VCode} (source : sourceOk f = true)
    (lowered : (match Stock.lower f with | .error _ => false | .ok result => decide (result.code = vc)) = true) :
    check f vc = true := by
  simp only [check,source,Bool.true_and]
  exact lowered

theorem check_of_comparison {f : Clif.Function} {vc : VCode} (checked : ComparisonCfg.check f vc = true) :
    check f vc = true := by
  simp only [ComparisonCfg.check,Bool.and_eq_true] at checked
  exact check_of_source (source_ok_of_comparison checked.1) checked.2

theorem check_of_comparison_imm {f : Clif.Function} {vc : VCode} (checked : ComparisonImmCfg.check f vc = true) :
    check f vc = true := by
  simp only [ComparisonImmCfg.check,Bool.and_eq_true] at checked
  exact check_of_source (source_ok_of_comparison_imm checked.1) checked.2

theorem check_of_comparison_zero {f : Clif.Function} {vc : VCode} (checked : ComparisonZeroCfg.check f vc = true) :
    check f vc = true := by
  simp only [ComparisonZeroCfg.check,Bool.and_eq_true] at checked
  exact check_of_source (source_ok_of_comparison_zero checked.1) checked.2

theorem check_of_conditional {f : Clif.Function} {vc : VCode} (checked : ConditionalCfg.check f vc = true) :
    check f vc = true := by
  simp only [ConditionalCfg.check,Bool.and_eq_true] at checked
  exact check_of_source (source_ok_of_conditional checked.1) checked.2

theorem check_of_conditional_ranked {f : Clif.Function} {vc : VCode}
    (checked : ConditionalCfg.rankedCheck f vc = true) : check f vc = true := by
  simp only [ConditionalCfg.rankedCheck,Bool.and_eq_true] at checked
  exact check_of_source (source_ok_of_conditional_ranked checked.1) checked.2

theorem check_of_forward {f : Clif.Function} {vc : VCode} (checked : ForwardCfg.check f vc = true) :
    check f vc = true := by
  simp only [ForwardCfg.check,Bool.and_eq_true] at checked
  exact check_of_source (source_ok_of_forward checked.1) checked.2

theorem check_of_parameter {f : Clif.Function} {vc : VCode} (checked : ParameterCfg.check f vc = true) :
    check f vc = true := by
  simp only [ParameterCfg.check,Bool.and_eq_true] at checked
  exact check_of_source (source_ok_of_parameter checked.1) checked.2

theorem check_of_parameter_loop {f : Clif.Function} {vc : VCode} (checked : ParameterLoopCfg.check f vc = true) :
    check f vc = true := by
  simp only [ParameterLoopCfg.check,Bool.and_eq_true] at checked
  exact check_of_source (source_ok_of_parameter_loop checked.1) checked.2

theorem check_of_comparison_loop {f : Clif.Function} {vc : VCode} (checked : ComparisonLoopCfg.check f vc = true) :
    check f vc = true := by
  simp only [ComparisonLoopCfg.check,Bool.and_eq_true] at checked
  exact check_of_source (source_ok_of_comparison_loop checked.1) checked.2

theorem check_of_comparison_computed_loop {f : Clif.Function} {vc : VCode}
    (checked : ComparisonComputedLoopCfg.check f vc = true) : check f vc = true := by
  simp only [ComparisonComputedLoopCfg.check,Bool.and_eq_true] at checked
  exact check_of_source (source_ok_of_comparison_computed_loop checked.1) checked.2

theorem check_of_linear {f : Clif.Function} {vc : VCode} (checked : LinearCfg.check f vc = true) :
    check f vc = true := by
  simp only [LinearCfg.check,Bool.and_eq_true] at checked
  exact check_of_source (source_ok_of_linear checked.1) checked.2

theorem check_of_two_block {f : Clif.Function} {vc : VCode} (checked : TwoBlock.check f vc = true) :
    check f vc = true := by
  simp only [TwoBlock.check,Bool.and_eq_true] at checked
  exact check_of_source (source_ok_of_two_block checked.1) checked.2

theorem check_of_two_block_entry {f : Clif.Function} {vc : VCode} (checked : TwoBlock.Entry.check f vc = true) :
    check f vc = true := by
  simp only [TwoBlock.Entry.check,Bool.and_eq_true] at checked
  exact check_of_source (source_ok_of_two_block_entry checked.1) checked.2

end Backend.Stock.ComparisonGeneralLoopCfg

namespace Backend.Stock.ComparisonComputedArgsLoopCfg
open Backend.Proof.Driver Backend.Stock.ComparisonGeneralLoopCfg
set_option autoImplicit false

/-! ### Split subsumption -/

/-- `sourceLeafEligible` from the control check of every block, the bodies and the ABI. -/
theorem source_leaf_eligible_of_blocks {f : Clif.Function}
    (controls : ∀ (bi : Nat) (b : Clif.Block),f.blocks[bi]? = some b → controlLeafEligible f bi b b.term = true)
    (bodies : f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) = true)
    (params : f.sig.params.all Scalar.narrowAbiEligible = true)
    (returns : f.sig.returns.all Scalar.narrowAbiEligible = true) : sourceLeafEligible f = true := by
  simp only [sourceLeafEligible,Bool.and_eq_true]
  refine ⟨⟨⟨?_,bodies⟩,params⟩,returns⟩
  apply List.all_eq_true.mpr
  rintro ⟨b,bi⟩ member
  exact controls bi b (List.mk_mem_zipIdx_iff_getElem?.mp member)

/-- `sourceOk` from `sourceLeafEligible` and the driver checks. -/
theorem source_ok_of_leaf {f : Clif.Function} (leaf : sourceLeafEligible f = true) (scope : lowerScopeB f = true)
    (dominated : dominatedB f = true) (abi : sigAbiOk f.sig = true) : sourceOk f = true := by
  simp only [sourceOk,leaf,scope,dominated,abi,Bool.and_self]

/-- **`ParameterArgsLoopCfg` (T7b-8) is in the class at the selector level.** -/
theorem source_leaf_eligible_of_parameter_args_loop {f : Clif.Function}
    (checked : ParameterArgsLoopCfg.sourceLeafEligible f = true) : sourceLeafEligible f = true := by
  simp only [ParameterArgsLoopCfg.sourceLeafEligible,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨controls,bodies⟩,params⟩,returns⟩ := checked
  refine source_leaf_eligible_of_blocks ?_ bodies params returns
  intro bi b found
  have old := List.all_eq_true.mp controls (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
  cases term : b.term <;> rw [term] at old
  case trap c => exact old
  case jump bc => exact old
  case ret xs => rfl
  case brif c yes no =>
    simp only [ParameterArgsLoopCfg.controlLeafEligible,ParameterArgsLoopCfg.controlEligible,
      Bool.and_eq_true] at old
    obtain ⟨⟨condition,yesNonentry⟩,noNonentry⟩ := old
    simp only [controlLeafEligible,controlEligible,condition_of_parameter condition,yesNonentry,noNonentry,
      Bool.and_self]
  all_goals
    simp only [ParameterArgsLoopCfg.controlLeafEligible,ParameterArgsLoopCfg.controlEligible] at old
    cases old

/-- **`ParameterArgsLoopCfg` (T7b-8) is in the class.** -/
theorem source_ok_of_parameter_args_loop {f : Clif.Function} (checked : ParameterArgsLoopCfg.sourceOk f = true) :
    sourceOk f = true := by
  simp only [ParameterArgsLoopCfg.sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨leaf,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_parameter_args_loop leaf) scope dominated abi

/-- **`ComparisonArgsLoopCfg` (T7b-9) is in the class at the selector level.** -/
theorem source_leaf_eligible_of_comparison_args_loop {f : Clif.Function}
    (checked : ComparisonArgsLoopCfg.sourceLeafEligible f = true) : sourceLeafEligible f = true := by
  simp only [ComparisonArgsLoopCfg.sourceLeafEligible,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨controls,bodies⟩,params⟩,returns⟩ := checked
  refine source_leaf_eligible_of_blocks ?_ bodies params returns
  intro bi b found
  have old := List.all_eq_true.mp controls (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
  cases term : b.term <;> rw [term] at old
  case trap c => exact old
  case jump bc => exact old
  case ret xs => rfl
  case brif c yes no =>
    simp only [ComparisonArgsLoopCfg.controlLeafEligible,ComparisonArgsLoopCfg.controlEligible,
      Bool.and_eq_true] at old
    obtain ⟨⟨condition,yesNonentry⟩,noNonentry⟩ := old
    simp only [controlLeafEligible,controlEligible,condition_of_loop condition,yesNonentry,noNonentry,
      Bool.and_self]
  all_goals
    simp only [ComparisonArgsLoopCfg.controlLeafEligible,ComparisonArgsLoopCfg.controlEligible] at old
    cases old

/-- **`ComparisonArgsLoopCfg` (T7b-9) is in the class.** -/
theorem source_ok_of_comparison_args_loop {f : Clif.Function} (checked : ComparisonArgsLoopCfg.sourceOk f = true) :
    sourceOk f = true := by
  simp only [ComparisonArgsLoopCfg.sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨leaf,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_comparison_args_loop leaf) scope dominated abi

/-- **`ParameterArgsCfg.anySourceOk` (ranked forward graphs whose parameter branches pass block
arguments to original or critical-edge successors) is in the class at the selector level.** -/
theorem source_leaf_eligible_of_parameter_any_args {f : Clif.Function}
    (checked : ParameterArgsCfg.anySourceLeafEligible f = true) : sourceLeafEligible f = true := by
  simp only [ParameterArgsCfg.anySourceLeafEligible,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨controls,bodies⟩,params⟩,returns⟩ := checked
  refine source_leaf_eligible_of_blocks ?_ bodies params returns
  intro bi b found
  have old := List.all_eq_true.mp controls (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
  cases term : b.term <;> rw [term] at old
  case trap c => exact old
  case jump bc => exact nonentry_of_after old
  case ret xs => rfl
  case brif c yes no =>
    simp only [ParameterArgsCfg.controlLeafEligible,ParameterArgsCfg.controlEligible,Bool.and_eq_true] at old
    obtain ⟨⟨condition,yesAfter⟩,noAfter⟩ := old
    simp only [controlLeafEligible,controlEligible,condition_of_parameter condition,nonentry_of_after yesAfter,
      nonentry_of_after noAfter,Bool.and_self]
  all_goals
    simp only [ParameterArgsCfg.controlLeafEligible,ParameterArgsCfg.controlEligible] at old
    cases old

/-- **`ParameterArgsCfg.anySourceOk` (ranked forward graphs whose parameter branches pass block
arguments to original or critical-edge successors) is in the class.** -/
theorem source_ok_of_parameter_any_args {f : Clif.Function} (checked : ParameterArgsCfg.anySourceOk f = true) :
    sourceOk f = true := by
  simp only [ParameterArgsCfg.anySourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨leaf,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_parameter_any_args leaf) scope dominated abi

/-- **`ParameterArgsCfg.sourceLeafEligible` (the same graphs in a lowered order without
critical-edge nodes) is in the class at the selector level.** -/
theorem source_leaf_eligible_of_parameter_args {f : Clif.Function}
    (checked : ParameterArgsCfg.sourceLeafEligible f = true) : sourceLeafEligible f = true := by
  simp only [ParameterArgsCfg.sourceLeafEligible,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨⟨controls,bodies⟩,params⟩,returns⟩,_⟩ := checked
  apply source_leaf_eligible_of_parameter_any_args
  simp only [ParameterArgsCfg.anySourceLeafEligible,controls,bodies,params,returns,Bool.and_self]

/-- **`ParameterArgsCfg.sourceOk` (the same graphs in a lowered order without critical-edge
nodes) is in the class.** -/
theorem source_ok_of_parameter_args {f : Clif.Function} (checked : ParameterArgsCfg.sourceOk f = true) :
    sourceOk f = true := by
  simp only [ParameterArgsCfg.sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨leaf,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_parameter_args leaf) scope dominated abi

/-- **The legacy class `ComparisonGeneralLoopCfg` (CB-10) is in the class**: it is this class
with empty `brif` arguments. -/
theorem source_leaf_eligible_of_general_loop {f : Clif.Function}
    (checked : ComparisonGeneralLoopCfg.sourceLeafEligible f = true) : sourceLeafEligible f = true := by
  simp only [ComparisonGeneralLoopCfg.sourceLeafEligible,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨controls,bodies⟩,params⟩,returns⟩ := checked
  refine source_leaf_eligible_of_blocks ?_ bodies params returns
  intro bi b found
  have old := List.all_eq_true.mp controls (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
  cases term : b.term <;> rw [term] at old
  case trap c => exact old
  case jump bc => exact old
  case ret xs => rfl
  case brif c yes no =>
    simp only [ComparisonGeneralLoopCfg.controlLeafEligible,ComparisonGeneralLoopCfg.controlEligible,
      Bool.and_eq_true] at old
    obtain ⟨⟨⟨⟨condition,_⟩,_⟩,yesNonentry⟩,noNonentry⟩ := old
    simp only [controlLeafEligible,controlEligible,condition,yesNonentry,noNonentry,Bool.and_self]
  all_goals
    simp only [ComparisonGeneralLoopCfg.controlLeafEligible,ComparisonGeneralLoopCfg.controlEligible] at old
    cases old

/-- **The legacy class `ComparisonGeneralLoopCfg` (CB-10) is in the class**: it is this class
with empty `brif` arguments. -/
theorem source_ok_of_general_loop {f : Clif.Function} (checked : ComparisonGeneralLoopCfg.sourceOk f = true) :
    sourceOk f = true := by
  simp only [ComparisonGeneralLoopCfg.sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨leaf,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_general_loop leaf) scope dominated abi

/-! ### Split checkers

Each split checker is `sourceOk f` and the equality of the edge split of the actual Stock code
with the published code, so `check` accepts it whenever `sourceOk` does. -/

private theorem check_of_source {f : Clif.Function} {vc : VCode} (source : sourceOk f = true)
    (lowered : (match Stock.lower f with
      | .error _ => false
      | .ok result => match splitEdgesChecked result.code result.edgeArgs with
        | .ok split => decide (split.code = vc)
        | .error _ => false) = true) :
    check f vc = true := by
  simp only [check,source,Bool.true_and]
  exact lowered

theorem check_of_parameter_args_loop {f : Clif.Function} {vc : VCode}
    (checked : ParameterArgsLoopCfg.check f vc = true) : check f vc = true := by
  simp only [ParameterArgsLoopCfg.check,Bool.and_eq_true] at checked
  exact check_of_source (source_ok_of_parameter_args_loop checked.1) checked.2

theorem check_of_comparison_args_loop {f : Clif.Function} {vc : VCode}
    (checked : ComparisonArgsLoopCfg.check f vc = true) : check f vc = true := by
  simp only [ComparisonArgsLoopCfg.check,Bool.and_eq_true] at checked
  exact check_of_source (source_ok_of_comparison_args_loop checked.1) checked.2

theorem check_of_parameter_any_args {f : Clif.Function} {vc : VCode}
    (checked : ParameterArgsCfg.anyCheck f vc = true) : check f vc = true := by
  simp only [ParameterArgsCfg.anyCheck,Bool.and_eq_true] at checked
  exact check_of_source (source_ok_of_parameter_any_args checked.1) checked.2

theorem check_of_parameter_args {f : Clif.Function} {vc : VCode}
    (checked : ParameterArgsCfg.check f vc = true) : check f vc = true := by
  simp only [ParameterArgsCfg.check,Bool.and_eq_true] at checked
  exact check_of_source (source_ok_of_parameter_args checked.1) checked.2

end Backend.Stock.ComparisonComputedArgsLoopCfg
