import FV.Backend.Lowering.StockGeneralLoopCfg6

/-! Subsumption of the CB-13 classes by the two classes of CB-14c (#140).

The split class `GeneralArgsLoopCfg6` accepts every function of the split class
`GeneralArgsLoopCfg5` (CB-13) and of the legacy class `GeneralLoopCfg6`; the legacy class
`GeneralLoopCfg6` accepts every function of the legacy class `GeneralLoopCfg5` (CB-13). The split
checkers publish the edge split of the actual Stock lowering and the legacy checkers its unsplit
code, so the subsumption also holds for the checkers. With the earlier subsumption lemmas, every
earlier split class is in `GeneralArgsLoopCfg6`, and every earlier legacy loop and branch class is
in `GeneralLoopCfg6`.

All proofs are Boolean reasoning over the `all`/`any` structure of the selectors. -/

namespace Backend.Stock.GeneralArgsLoopCfg6
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

/-- **`GeneralArgsLoopCfg5` (CB-13) is in the class at the selector level.** -/
theorem source_leaf_eligible_of_general_args_loop {f : Clif.Function}
    (checked : GeneralArgsLoopCfg5.sourceLeafEligible f = true) : sourceLeafEligible f = true := by
  simp only [GeneralArgsLoopCfg5.sourceLeafEligible,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨controls,bodies⟩,params⟩,returns⟩ := checked
  refine source_leaf_eligible_of_blocks ?_ bodies params returns
  intro bi b found
  have old := List.all_eq_true.mp controls (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
  cases term : b.term <;> rw [term] at old
  case trap c => exact old
  case jump bc => exact old
  case ret xs => rfl
  case brif c yes no => exact old
  all_goals
    simp only [GeneralArgsLoopCfg5.controlLeafEligible,GeneralArgsLoopCfg5.controlEligible] at old
    cases old

/-- **`GeneralArgsLoopCfg5` (CB-13) is in the class.** -/
theorem source_ok_of_general_args_loop {f : Clif.Function}
    (checked : GeneralArgsLoopCfg5.sourceOk f = true) : sourceOk f = true := by
  simp only [GeneralArgsLoopCfg5.sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨leaf,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_general_args_loop leaf) scope dominated abi

/-- **The legacy class `GeneralLoopCfg6` is in the class at the selector level**: it is this class
with empty `brif` and `br_table` arguments. -/
theorem source_leaf_eligible_of_general_loop {f : Clif.Function}
    (checked : GeneralLoopCfg6.sourceLeafEligible f = true) : sourceLeafEligible f = true := by
  simp only [GeneralLoopCfg6.sourceLeafEligible,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨controls,bodies⟩,params⟩,returns⟩ := checked
  refine source_leaf_eligible_of_blocks ?_ bodies params returns
  intro bi b found
  have old := List.all_eq_true.mp controls (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
  cases term : b.term <;> rw [term] at old
  case trap c => exact old
  case jump bc => exact old
  case ret xs => rfl
  case brif c yes no =>
    simp only [GeneralLoopCfg6.controlLeafEligible,GeneralLoopCfg6.controlEligible,
      GeneralLoopCfg5.controlEligible,Bool.and_eq_true] at old
    obtain ⟨⟨⟨⟨condition,_⟩,_⟩,yesNonentry⟩,noNonentry⟩ := old
    simp only [controlLeafEligible,controlEligible,GeneralArgsLoopCfg5.controlEligible,condition,yesNonentry,
      noNonentry,Bool.and_self]
  case brTable x dc tbl =>
    simp only [GeneralLoopCfg6.controlLeafEligible,GeneralLoopCfg6.controlEligible,Bool.and_eq_true] at old
    simp only [controlLeafEligible,controlEligible,old.1]
  all_goals
    simp only [GeneralLoopCfg6.controlLeafEligible,GeneralLoopCfg6.controlEligible,
      GeneralLoopCfg5.controlEligible] at old
    cases old

/-- **The legacy class `GeneralLoopCfg6` is in the class.** -/
theorem source_ok_of_general_loop {f : Clif.Function} (checked : GeneralLoopCfg6.sourceOk f = true) :
    sourceOk f = true := by
  simp only [GeneralLoopCfg6.sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨leaf,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_general_loop leaf) scope dominated abi

/-- **The checker of `GeneralArgsLoopCfg5` (CB-13) is in the checker of the class**: both
publish the edge split of the actual Stock lowering. -/
theorem check_of_general_args_loop {f : Clif.Function} {vc : VCode}
    (checked : GeneralArgsLoopCfg5.check f vc = true) : check f vc = true := by
  simp only [GeneralArgsLoopCfg5.check,Bool.and_eq_true] at checked
  simp only [check,source_ok_of_general_args_loop checked.1,Bool.true_and]
  exact checked.2

end Backend.Stock.GeneralArgsLoopCfg6

namespace Backend.Stock.GeneralLoopCfg6
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

/-- **The legacy class `GeneralLoopCfg5` (CB-13) is in the class at the selector level.** -/
theorem source_leaf_eligible_of_general_loop {f : Clif.Function}
    (checked : GeneralLoopCfg5.sourceLeafEligible f = true) : sourceLeafEligible f = true := by
  simp only [GeneralLoopCfg5.sourceLeafEligible,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨controls,bodies⟩,params⟩,returns⟩ := checked
  refine source_leaf_eligible_of_blocks ?_ bodies params returns
  intro bi b found
  have old := List.all_eq_true.mp controls (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
  cases term : b.term <;> rw [term] at old
  case trap c => exact old
  case jump bc => exact old
  case ret xs => rfl
  case brif c yes no => exact old
  all_goals
    simp only [GeneralLoopCfg5.controlLeafEligible,GeneralLoopCfg5.controlEligible] at old
    cases old

/-- **The legacy class `GeneralLoopCfg5` (CB-13) is in the class.** -/
theorem source_ok_of_general_loop {f : Clif.Function} (checked : GeneralLoopCfg5.sourceOk f = true) :
    sourceOk f = true := by
  simp only [GeneralLoopCfg5.sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨leaf,scope⟩,dominated⟩,abi⟩ := checked
  exact source_ok_of_leaf (source_leaf_eligible_of_general_loop leaf) scope dominated abi

/-- **The checker of `GeneralLoopCfg5` (CB-13) is in the checker of the class**: both publish the
unsplit code of the actual Stock lowering. -/
theorem check_of_general_loop {f : Clif.Function} {vc : VCode}
    (checked : GeneralLoopCfg5.check f vc = true) : check f vc = true := by
  simp only [GeneralLoopCfg5.check,Bool.and_eq_true] at checked
  simp only [check,source_ok_of_general_loop checked.1,Bool.true_and]
  exact checked.2

end Backend.Stock.GeneralLoopCfg6
