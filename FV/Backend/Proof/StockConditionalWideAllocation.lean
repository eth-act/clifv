import FV.Backend.Proof.StockDemandExtent
import FV.Backend.Proof.StockSelectNonzeroWideShape
import FV.Backend.Proof.StockSelectConditionCalls
import FV.Backend.Proof.StockConditionalValues
import FV.Backend.Proof.StockConditionalCalls

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program

private theorem nonzero_wide_emission {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (wide : Bool) {c : Nat}
    (typed : ctx.valueType? c = some (.int (if wide then 64 else 32)))
    {conditionFuel constructFuel emitFuel : Nat}
    (enoughCondition : 220 ≤ conditionFuel) (enoughConstruct : 100 ≤ constructFuel) (enoughEmit : 30 ≤ emitFuel)
    {before middle constructed next : State} {trace helperTrace conditionTrace constructTrace final : Array RuleId}
    {raw descriptor out : V} {yes no : Label}
    (conditionRun : ApplyInternal program (Stock.sem ctx) {} conditionFuel 123 651 [.value c]
      (before,trace) raw (middle,helperTrace))
    (constructRun : ApplyInternal program (Stock.sem ctx) {} constructFuel 46 722
      [raw,.label yes,.label no] (middle,conditionTrace) descriptor (constructed,constructTrace))
    (emitRun : ApplyInternal program (Stock.sem ctx) {} emitFuel 13 242
      [descriptor] (constructed,constructTrace) out (next,final)) :
    ∃ inst,next.base = before.base.emit inst := by
  obtain ⟨allowed,key,mapped,rawEq,middleEq⟩ :=
    ScalarSelect.stock_select_nonzero_wide_emitter_observed inv wide enoughCondition typed conditionRun
  let size : OperandSize := if wide then .size64 else .size32
  have decoded : OperandSize.ofIdx? (if wide then 1 else 0) = some size := by cases wide <;> rfl
  have shape : CondShape raw (fun _ => True) := .inr (.inl ⟨key,_,size,rawEq,decoded,trivial⟩)
  obtain ⟨base,descriptorEq⟩ := descriptor_shape rfl enoughConstruct shape constructRun
  have projected := BranchHelpers.stock_emit_side_effect_projects ctx {} rfl (emitFuel+1)
    [descriptor] constructed constructTrace
  have legacy : ApplyInternal program (Backend.sem ctx) {} emitFuel 13 242
      [descriptor] (constructed.base,constructTrace) out (next.base,final) := by
    unfold ApplyInternal at emitRun ⊢
    rw [emitRun] at projected
    exact projected.symm
  rw [base,descriptorEq,rawEq] at legacy
  dsimp only [brCondV] at legacy
  obtain ⟨inst,decodedInst,finish,unit⟩ := emit_side_effect_inst_ok data_program rfl enoughEmit legacy
  dsimp only at finish
  rw [middleEq] at finish
  exact ⟨inst,finish⟩

/-- The actual wide nonzero helpers allocate no virtual registers. -/
theorem nonzero_wide_allocation {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (wide : Bool) {c : Nat}
    (typed : ctx.valueType? c = some (.int (if wide then 64 else 32)))
    {conditionFuel constructFuel emitFuel : Nat}
    (enoughCondition : 220 ≤ conditionFuel) (enoughConstruct : 100 ≤ constructFuel) (enoughEmit : 30 ≤ emitFuel)
    {before middle constructed next : State} {trace helperTrace conditionTrace constructTrace final : Array RuleId}
    {raw descriptor out : V} {yes no : Label}
    (conditionRun : ApplyInternal program (Stock.sem ctx) {} conditionFuel 123 651 [.value c]
      (before,trace) raw (middle,helperTrace))
    (constructRun : ApplyInternal program (Stock.sem ctx) {} constructFuel 46 722
      [raw,.label yes,.label no] (middle,conditionTrace) descriptor (constructed,constructTrace))
    (emitRun : ApplyInternal program (Stock.sem ctx) {} emitFuel 13 242
      [descriptor] (constructed,constructTrace) out (next,final)) :
    next.base.nextVreg = before.base.nextVreg := by
  obtain ⟨inst,finish⟩ := nonzero_wide_emission inv wide typed enoughCondition enoughConstruct enoughEmit
    conditionRun constructRun emitRun
  rw [finish]
  rfl

/-- The real wide branch emitter appends exactly one instruction. -/
theorem nonzero_wide_emitted_size {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (wide : Bool) {c : Nat}
    (typed : ctx.valueType? c = some (.int (if wide then 64 else 32)))
    {conditionFuel constructFuel emitFuel : Nat}
    (enoughCondition : 220 ≤ conditionFuel) (enoughConstruct : 100 ≤ constructFuel) (enoughEmit : 30 ≤ emitFuel)
    {before middle constructed next : State} {trace helperTrace conditionTrace constructTrace final : Array RuleId}
    {raw descriptor out : V} {yes no : Label}
    (conditionRun : ApplyInternal program (Stock.sem ctx) {} conditionFuel 123 651 [.value c]
      (before,trace) raw (middle,helperTrace))
    (constructRun : ApplyInternal program (Stock.sem ctx) {} constructFuel 46 722
      [raw,.label yes,.label no] (middle,conditionTrace) descriptor (constructed,constructTrace))
    (emitRun : ApplyInternal program (Stock.sem ctx) {} emitFuel 13 242
      [descriptor] (constructed,constructTrace) out (next,final)) :
    next.base.emitted.size = before.base.emitted.size+1 := by
  obtain ⟨inst,finish⟩ := nonzero_wide_emission inv wide typed enoughCondition enoughConstruct enoughEmit
    conditionRun constructRun emitRun
  rw [finish]
  exact Array.size_push inst

end Backend.Stock.Proof.ConditionalValues

namespace Backend.Stock.Proof.ConditionalCalls
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 ConditionalValues
set_option autoImplicit false
set_option Elab.async false

/-- The actual selected parameter branch preserves both its allocation
frontier and source-demand extent through all three helper calls. -/
theorem Calls.parameter_wide_bounds {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c) (wide : Bool)
    (typed : ctx.valueType? c = some (.int (if wide then 64 else 32)))
    (parameter : ctx.defInst? c = none) :
    next.base.nextVreg = before.base.nextVreg ∧ next.demand.size = before.demand.size := by
  have size := (Extent.apply_demand_size calls.emitRun).trans
    ((Extent.apply_demand_size calls.constructRun).trans (Extent.apply_demand_size calls.conditionRun))
  have conditionRun := calls.conditionRun
  rw [source] at conditionRun
  rcases ScalarSelect.stock_original_select_condition_calls inv calls.conditionEnough conditionRun with
    ⟨helperFuel,helperTrace,enough,nonzero⟩ |
    ⟨cc,ty,a,b,origin,helperFuel,helperTrace,enough,comparison⟩
  · exact ⟨nonzero_wide_allocation inv wide typed (by omega) calls.constructEnough calls.emitEnough
      nonzero calls.constructRun calls.emitRun,size⟩
  · simp [ScalarSelect.SelectComparisonOrigin,Ctx.defClif?,parameter] at origin

/-- The selected original parameter call appends exactly its real branch. -/
theorem Calls.parameter_wide_emitted_size {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c) (wide : Bool)
    (typed : ctx.valueType? c = some (.int (if wide then 64 else 32)))
    (parameter : ctx.defInst? c = none) :
    next.base.emitted.size = before.base.emitted.size+1 := by
  have conditionRun := calls.conditionRun
  rw [source] at conditionRun
  rcases ScalarSelect.stock_original_select_condition_calls inv calls.conditionEnough conditionRun with
    ⟨helperFuel,helperTrace,enough,nonzero⟩ |
    ⟨cc,ty,a,b,origin,helperFuel,helperTrace,enough,comparison⟩
  · exact nonzero_wide_emitted_size inv wide typed (by omega) calls.constructEnough calls.emitEnough
      nonzero calls.constructRun calls.emitRun
  · simp [ScalarSelect.SelectComparisonOrigin,Ctx.defClif?,parameter] at origin

end Backend.Stock.Proof.ConditionalCalls
