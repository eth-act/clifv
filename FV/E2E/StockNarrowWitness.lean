import FV.E2E.CompiledSemanticNI
import FV.E2E.StockNarrowChecks
namespace E2E.StockNarrowNIWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Extract complete artifacts from the same checks used by the fixed grid. -/
theorem compiled_of_checks {f : Clif.Function} {cleanup : Bool} (checked : checks f cleanup = true) :
    Stock.Scalar.Domain f ∧
    ∃ result vcp rf af fa fb,
      CompiledStockArithmeticStage f cleanup 0 result vcp rf af fa fb ∧
      CompiledSemanticNI f 0 result.code vcp rf af fa fb ∧
      Stock.Scalar.lowerValidated f = .ok result.code ∧
      DivBoundary.check f.sig result.code = true ∧
      leanAlloc vcp = .ok rf ∧ FormsCovered ⟨fa.k,af.slotBase⟩ vcp := by
  simp only [checks,Bool.and_eq_true] at checked
  obtain ⟨source,h⟩ := checked
  have domain := Stock.Scalar.sourceOk_sound source
  refine ⟨domain,?_⟩
  cases lowered : Stock.lower f with
  | error message => simp [lowered] at h
  | ok result =>
    simp only [lowered,Bool.and_eq_true,Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨reads,scalar⟩,paired⟩,actual⟩,h⟩ := h
    have actualLower : Stock.Scalar.lowerValidated f = .ok result.code := by
      cases observed : Stock.Scalar.lowerValidated f with
      | error message => simp [observed] at actual
      | ok vc =>
        simp only [observed,decide_eq_true_eq] at actual
        cases actual
        rfl
    cases prepared : Backend.prepare (Stock.Arithmetic.stage cleanup result.code) with
    | error message => simp [prepared] at h
    | ok vcp =>
      simp only [prepared,Bool.and_eq_true] at h
      obtain ⟨prepOk,h⟩ := h
      cases allocated : leanAlloc vcp with
      | error message => simp [allocated] at h
      | ok rf =>
        simp only [allocated,Bool.and_eq_true] at h
        obtain ⟨checked,h⟩ := h
        cases physical : lowerRFunc vcp rf with
        | error message => simp [physical] at h
        | ok af =>
          cases emitted : emitFunc 0 af with
          | error message => simp [physical,emitted] at h
          | ok fa =>
            simp only [physical,emitted,Bool.and_eq_true] at h
            obtain ⟨covered,layoutOk⟩ := h
            cases emittedLayout : fa.layout with
            | error message => rw [emittedLayout] at layoutOk; change false = true at layoutOk; cases layoutOk
            | ok fb =>
              have check : checkAlloc vcp rf = .ok () := by
                cases check : checkAlloc vcp rf with
                | error message => rw [check] at checked; change false = true at checked; cases checked
                | ok value => cases value; rfl
              have stage : CompiledStockArithmeticStage f cleanup 0 result vcp rf af fa fb :=
                ⟨lowered,prepared,prepOk,check,physical,emitted,emittedLayout⟩
              exact ⟨result,vcp,rf,af,fa,fb,stage,.scalarDiv domain rfl reads stage,
                actualLower,reads,allocated,(formsCoveredB_iff _ _).mp covered⟩

private theorem grids_true : primitiveGrid = true ∧ mixedGrid = true := by
  simpa only [grid,Bool.and_eq_true] using checks_true

private theorem primitive_grid_entry {config : Configuration} (hc : config ∈ conventions)
    {ty : Clif.Ty} (ht : ty ∈ widths) {c : Case} (member : c ∈ cases ty)
    (scope : lowerScopeB (function config c) = true) :
    sourceCases (function config c) c.inputTy = true ∧ primitiveTraps config c = true ∧
      checks (function config c) false = true ∧ checks (function config c) true = true := by
  have h := grids_true.1
  change conventions.all _ = true at h
  have h := List.all_eq_true.mp h config hc
  have h := List.all_eq_true.mp h ty ht
  have h := List.all_eq_true.mp h c member
  by_cases excluded : outsideOriginalScope c = true
  · simp only [excluded,↓reduceIte,Bool.and_eq_true,Bool.not_eq_true'] at h
    have impossible := h.1
    rw [scope] at impossible
    cases impossible
  · have no : outsideOriginalScope c = false := Bool.eq_false_iff.mpr excluded
    simp only [no,Bool.false_eq_true,↓reduceIte,Bool.and_eq_true] at h
    exact ⟨h.1.1.1,h.1.1.2,h.1.2,h.2⟩

/-- Every originally in-scope primitive fixture has a complete checked pipeline. -/
theorem compiled_exists {config : Configuration} (hc : config ∈ conventions)
    {ty : Clif.Ty} (ht : ty ∈ widths) {c : Case} (member : c ∈ cases ty)
    (scope : lowerScopeB (function config c) = true) (cleanup : Bool) :
    Stock.Scalar.Domain (function config c) ∧
    ∃ result vcp rf af fa fb,
      CompiledStockArithmeticStage (function config c) cleanup 0 result vcp rf af fa fb ∧
      CompiledSemanticNI (function config c) 0 result.code vcp rf af fa fb ∧
      Stock.Scalar.lowerValidated (function config c) = .ok result.code ∧
      DivBoundary.check (function config c).sig result.code = true ∧
      leanAlloc vcp = .ok rf ∧ FormsCovered ⟨fa.k,af.slotBase⟩ vcp := by
  have h := primitive_grid_entry hc ht member scope
  apply compiled_of_checks
  cases cleanup with
  | false => exact h.2.2.1
  | true => exact h.2.2.2

/-- Mixed narrow/wide casts and consumed/unused divisions inhabit the same full contract. -/
theorem compiled_mixed_exists {config : Configuration} (hc : config ∈ conventions)
    {ty : Clif.Ty} (ht : ty ∈ widths) (cleanup : Bool) :
    Stock.Scalar.Domain (mixedFunction config ty) ∧
    ∃ result vcp rf af fa fb,
      CompiledStockArithmeticStage (mixedFunction config ty) cleanup 0 result vcp rf af fa fb ∧
      CompiledSemanticNI (mixedFunction config ty) 0 result.code vcp rf af fa fb ∧
      Stock.Scalar.lowerValidated (mixedFunction config ty) = .ok result.code ∧
      DivBoundary.check (mixedFunction config ty).sig result.code = true ∧
      leanAlloc vcp = .ok rf ∧ FormsCovered ⟨fa.k,af.slotBase⟩ vcp := by
  have h := grids_true.2
  change conventions.all _ = true at h
  have h := List.all_eq_true.mp h config hc
  have h := List.all_eq_true.mp h ty ht
  simp only [Bool.and_eq_true] at h
  apply compiled_of_checks
  cases cleanup with
  | false => exact h.1.2
  | true => exact h.2

/-- Nonvacuity: actual original source executions return or trap, rather than get stuck. -/
theorem source_outcomes {config : Configuration} (hc : config ∈ conventions)
    {ty : Clif.Ty} (ht : ty ∈ widths) {c : Case} (member : c ∈ cases ty)
    (scope : lowerScopeB (function config c) = true) {sample : Nat} (sampleIn : sample ∈ [0,1,2]) :
    (∃ vals mem,sourceRun (function config c) c.inputTy sample = .returned vals mem) ∨
      ∃ code,sourceRun (function config c) c.inputTy sample = .trapped code := by
  have h := (primitive_grid_entry hc ht member scope).1
  simp only [sourceCases,Bool.and_eq_true] at h
  have h := List.all_eq_true.mp h.1 sample sampleIn
  cases outcome : sourceRun (function config c) c.inputTy sample with
  | returned vals mem => exact Or.inl ⟨vals,mem,rfl⟩
  | trapped code => exact Or.inr ⟨code,rfl⟩
  | stuck message => simp [outcome,completed] at h
  | outOfFuel => simp [outcome,completed] at h

/-- Every positive primitive source sample really returns. -/
theorem source_return {config : Configuration} (hc : config ∈ conventions)
    {ty : Clif.Ty} (ht : ty ∈ widths) {c : Case} (member : c ∈ cases ty)
    (scope : lowerScopeB (function config c) = true) :
    ∃ vals mem,sourceRun (function config c) c.inputTy 1 = .returned vals mem := by
  have h := (primitive_grid_entry hc ht member scope).1
  simp only [sourceCases,Bool.and_eq_true] at h
  have h := h.2
  cases outcome : sourceRun (function config c) c.inputTy 1 with
  | returned vals mem => exact ⟨vals,mem,rfl⟩
  | trapped code => simp [outcome,returned] at h
  | stuck message => simp [outcome,returned] at h
  | outOfFuel => simp [outcome,returned] at h

private theorem trapped_sound {code : Clif.TrapCode} {outcome : Clif.Outcome}
    (h : trapped code outcome = true) : outcome = .trapped code := by
  cases outcome with
  | trapped observed =>
    have equal : code = observed := beq_iff_eq.mp h
    cases equal
    rfl
  | _ => cases h

/-- Real original-source zero-divisor traps, including unused-result operations. -/
theorem division_zero {config : Configuration} (hc : config ∈ conventions)
    {ty : Clif.Ty} (ht : ty ∈ widths) {c : Case} (member : c ∈ cases ty)
    (scope : lowerScopeB (function config c) = true)
    {op : Clif.DivOp} {divisionTy : Clif.Ty} {x y : Nat} (inst : c.inst = .div op divisionTy x y) :
    sourceRun (function config c) c.inputTy 0 = .trapped .intDivz := by
  have h := (primitive_grid_entry hc ht member scope).2.1
  simp only [primitiveTraps,inst,Bool.and_eq_true] at h
  exact trapped_sound h.1

/-- Real original-source signed minimum / -1 overflow, with the original values. -/
theorem division_overflow {config : Configuration} (hc : config ∈ conventions)
    {ty : Clif.Ty} (ht : ty ∈ widths) {c : Case} (member : c ∈ cases ty)
    (scope : lowerScopeB (function config c) = true)
    {divisionTy : Clif.Ty} {x y : Nat} (inst : c.inst = .div .sdiv divisionTy x y) :
    sourceRun (function config c) c.inputTy 2 = .trapped .intOvf := by
  have h := (primitive_grid_entry hc ht member scope).2.1
  simp only [primitiveTraps,inst,beq_self_eq_true,↓reduceIte,Bool.and_eq_true] at h
  exact trapped_sound h.2

/-- Entry keeps arbitrary source argument bits and the explicit slot address. -/
theorem source_entry (config : Configuration) (c : Case)
    (input : Nat → BitVec c.inputTy.width) (slot : Nat) :
    ClifEntry (function config c) (arguments c.inputTy input)
      ⟨frame (function config c) c.inputTy input slot,[],Clif.Mem.empty⟩ := by
  cases config <;> exact ⟨rfl,rfl,rfl,⟨_,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩

theorem mixed_source_entry (config : Configuration) (ty : Clif.Ty)
    (input : Nat → BitVec ty.width) (slot : Nat) :
    ClifEntry (mixedFunction config ty) (arguments ty input)
      ⟨frame (mixedFunction config ty) ty input slot,[],Clif.Mem.empty⟩ := by
  cases config <;> exact ⟨rfl,rfl,rfl,⟨_,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩

end E2E.StockNarrowNIWitness
