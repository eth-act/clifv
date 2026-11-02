import FV.Backend.Lowering.StockGeneralLoopCfg3

/-! Subsumption of the CB-11 classes by the two classes of CB-12 (#140).

The legacy class `GeneralLoopCfg3` accepts every function of the legacy class `GeneralLoopCfg2`
(CB-11), and the split class `GeneralArgsLoopCfg3` accepts every function of the split class
`GeneralArgsLoopCfg2` (CB-11) and of `GeneralLoopCfg3`. The legacy checkers publish the unsplit
code of the actual Stock lowering and the split checkers its edge split, so the subsumption also
holds for the checkers. With the CB-11 subsumption lemmas (`StockGeneralSubsumption2`), every
earlier legacy loop and branch class is in `GeneralLoopCfg3`, and every earlier split class is in
`GeneralArgsLoopCfg3`.

All proofs are Boolean reasoning over the `all`/`any` structure of the selectors. -/

namespace Backend.Stock.GeneralArgsLoopCfg3
open Backend.Proof.Driver
set_option autoImplicit false

/-- The conditions of `GeneralArgsLoopCfg2` are conditions of the class. -/
theorem condition_of_general_args {f : Clif.Function} {b : Clif.Block} {c : Nat}
    (computed : GeneralArgsLoopCfg2.conditionEligible f b c = true) :
    conditionEligible f b c = true := by
  simp only [conditionEligible,computed,Bool.true_or]

/-- A narrow condition is a condition of the class. -/
theorem condition_of_narrow {f : Clif.Function} {b : Clif.Block} {c : Nat}
    (plain : narrowEligible f c = true) : conditionEligible f b c = true := by
  simp only [conditionEligible,plain,Bool.or_true]

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

/-- **`GeneralArgsLoopCfg2` (CB-11) is in the class at the selector level.** -/
theorem source_leaf_eligible_of_general_args_loop {f : Clif.Function}
    (checked : GeneralArgsLoopCfg2.sourceLeafEligible f = true) : sourceLeafEligible f = true := by
  simp only [GeneralArgsLoopCfg2.sourceLeafEligible,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨controls,bodies⟩,params⟩,returns⟩ := checked
  refine source_leaf_eligible_of_blocks ?_ bodies params returns
  intro bi b found
  have old := List.all_eq_true.mp controls (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
  cases term : b.term <;> rw [term] at old
  case trap c => exact old
  case jump bc => exact old
  case ret xs => rfl
  case brif c yes no =>
    simp only [GeneralArgsLoopCfg2.controlLeafEligible,GeneralArgsLoopCfg2.controlEligible,
      Bool.and_eq_true] at old
    obtain ⟨⟨condition,yesNonentry⟩,noNonentry⟩ := old
    simp only [controlLeafEligible,controlEligible,condition_of_general_args condition,yesNonentry,noNonentry,
      Bool.and_self]
  all_goals
    simp only [GeneralArgsLoopCfg2.controlLeafEligible,GeneralArgsLoopCfg2.controlEligible] at old
    cases old

/-- **`GeneralArgsLoopCfg2` (CB-11) is in the class.** -/
theorem source_ok_of_general_args_loop {f : Clif.Function}
    (checked : GeneralArgsLoopCfg2.sourceOk f = true) : sourceOk f = true := by
  simp only [GeneralArgsLoopCfg2.sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨leaf,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_general_args_loop leaf) scope dominated abi

/-- **The legacy class `GeneralLoopCfg3` is in the class at the selector level**: it is this class
with empty `brif` arguments. -/
theorem source_leaf_eligible_of_general_loop {f : Clif.Function}
    (checked : GeneralLoopCfg3.sourceLeafEligible f = true) : sourceLeafEligible f = true := by
  simp only [GeneralLoopCfg3.sourceLeafEligible,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨controls,bodies⟩,params⟩,returns⟩ := checked
  refine source_leaf_eligible_of_blocks ?_ bodies params returns
  intro bi b found
  have old := List.all_eq_true.mp controls (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
  cases term : b.term <;> rw [term] at old
  case trap c => exact old
  case jump bc => exact old
  case ret xs => rfl
  case brif c yes no =>
    simp only [GeneralLoopCfg3.controlLeafEligible,GeneralLoopCfg3.controlEligible,Bool.and_eq_true] at old
    obtain ⟨⟨⟨⟨condition,_⟩,_⟩,yesNonentry⟩,noNonentry⟩ := old
    simp only [controlLeafEligible,controlEligible,condition,yesNonentry,noNonentry,Bool.and_self]
  all_goals
    simp only [GeneralLoopCfg3.controlLeafEligible,GeneralLoopCfg3.controlEligible] at old
    cases old

/-- **The legacy class `GeneralLoopCfg3` is in the class.** -/
theorem source_ok_of_general_loop {f : Clif.Function} (checked : GeneralLoopCfg3.sourceOk f = true) :
    sourceOk f = true := by
  simp only [GeneralLoopCfg3.sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨leaf,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_general_loop leaf) scope dominated abi

/-! ### Split checkers -/

private theorem check_of_source {f : Clif.Function} {vc : VCode} (source : sourceOk f = true)
    (lowered : (match Stock.lower f with
      | .error _ => false
      | .ok result => match splitEdgesChecked result.code result.edgeArgs with
        | .ok split => decide (split.code = vc)
        | .error _ => false) = true) :
    check f vc = true := by
  simp only [check,source,Bool.true_and]
  exact lowered

/-- **The checker of `GeneralArgsLoopCfg2` (CB-11) is in the checker of the class**: both
publish the edge split of the actual Stock lowering. -/
theorem check_of_general_args_loop {f : Clif.Function} {vc : VCode}
    (checked : GeneralArgsLoopCfg2.check f vc = true) : check f vc = true := by
  simp only [GeneralArgsLoopCfg2.check,Bool.and_eq_true] at checked
  exact check_of_source (source_ok_of_general_args_loop checked.1) checked.2

end Backend.Stock.GeneralArgsLoopCfg3

namespace Backend.Stock.GeneralLoopCfg3
open Backend.Proof.Driver
set_option autoImplicit false

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

/-- **The legacy class `GeneralLoopCfg2` (CB-11) is in the class at the selector
level.** -/
theorem source_leaf_eligible_of_general_loop {f : Clif.Function}
    (checked : GeneralLoopCfg2.sourceLeafEligible f = true) : sourceLeafEligible f = true := by
  simp only [GeneralLoopCfg2.sourceLeafEligible,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨controls,bodies⟩,params⟩,returns⟩ := checked
  refine source_leaf_eligible_of_blocks ?_ bodies params returns
  intro bi b found
  have old := List.all_eq_true.mp controls (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
  cases term : b.term <;> rw [term] at old
  case trap c => exact old
  case jump bc => exact old
  case ret xs => rfl
  case brif c yes no =>
    simp only [GeneralLoopCfg2.controlLeafEligible,GeneralLoopCfg2.controlEligible,
      Bool.and_eq_true] at old
    obtain ⟨⟨⟨⟨condition,yesEmpty⟩,noEmpty⟩,yesNonentry⟩,noNonentry⟩ := old
    simp only [controlLeafEligible,controlEligible,GeneralArgsLoopCfg3.condition_of_general_args condition,
      yesEmpty,noEmpty,yesNonentry,noNonentry,Bool.and_self]
  all_goals
    simp only [GeneralLoopCfg2.controlLeafEligible,GeneralLoopCfg2.controlEligible] at old
    cases old

/-- **The legacy class `GeneralLoopCfg2` (CB-11) is in the class.** -/
theorem source_ok_of_general_loop {f : Clif.Function} (checked : GeneralLoopCfg2.sourceOk f = true) :
    sourceOk f = true := by
  simp only [GeneralLoopCfg2.sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨leaf,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_general_loop leaf) scope dominated abi

/-- **The checker of `GeneralLoopCfg2` (CB-11) is in the checker of the class**: both
publish the unsplit code of the actual Stock lowering. -/
theorem check_of_general_loop {f : Clif.Function} {vc : VCode}
    (checked : GeneralLoopCfg2.check f vc = true) : check f vc = true := by
  simp only [GeneralLoopCfg2.check,Bool.and_eq_true] at checked
  simp only [check,source_ok_of_general_loop checked.1,Bool.true_and]
  exact checked.2

end Backend.Stock.GeneralLoopCfg3
