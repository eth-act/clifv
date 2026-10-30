import FV.Backend.Proof.StockCmpWideActualValues
import FV.Backend.Proof.StockCmpNarrowActualAllocation
import FV.Backend.Proof.StockCmpRootMatch
import FV.Backend.Proof.StockCmpOutput
import FV.Backend.Proof.StockSelectComparisonConditionShape
import FV.Backend.Proof.StockSelectCompanionFragment
import FV.Backend.Proof.StockCmpResultWidth
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private def ActualRootCalls (p : Program) (ctx : Ctx) (cc : Clif.IntCC) (x y : Nat)
    (st next : State) (tr trace : Array RuleId) (out : V) : Prop :=
  ∃ emitFuel conditionFuel outputFuel condition middle emitTrace value produced conditionTrace,
    300 ≤ emitFuel ∧ 119 ≤ conditionFuel ∧ 100 ≤ outputFuel ∧
    ApplyInternal p (Stock.sem ctx) {} emitFuel 123 652 [.data 145 (ccIdx cc) [],.value x,.value y]
      (st,tr) condition (middle,emitTrace) ∧
    ApplyInternal p (Stock.sem ctx) {} conditionFuel 27 715 [condition]
      (middle,emitTrace) value (produced,conditionTrace) ∧
    ApplyInternal p (Stock.sem ctx) {} outputFuel 25 172 [value]
      (produced,conditionTrace) out (next,trace)
/-- Successful actual comparison RHS execution exposes all three real helper
calls and their complete intermediate states, without caller helper certificates. -/
private theorem actual_root_rhs_calls {p : Program} (hp : Data p) (ctx : Ctx)
    (cc : Clif.IntCC) (x y : Nat) {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} 999999 rule_lower_1281.rhs (cmpEnv cc x y)).run
      (st,tr) = .ok (some out,next,trace)) : ActualRootCalls p ctx cc x y st next tr trace out := by
  have hc : ({} : Config).checkOverlap = false := rfl
  cases hp
  isel_inv [*,rule_lower_1281,cmpEnv,env3] at run
  isel_destruct
  subst_vars
  rename_i value produced condition middle outputCall conditionCall emitCall
  exact ⟨999993,999995,999997,condition,middle.1,middle.2,value,produced.1,produced.2,
    by decide,by decide,by decide,emitCall,conditionCall,outputCall⟩

/-- The actual fused zero-extension RHS computes the comparison and its full
zero-extension, for all original scalar operand/output widths. It reuses the
comparison emitter proofs and derives the final CSET shape from actual calls.
Empty emission and scratch separation are supplied by retained-record invariants. -/
theorem stock_cast_cmp_rhs_source_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cc : Clif.IntCC} {ty outTy : Clif.Ty}
    (accepted : eTy ty = true) (outputAccepted : eTy outTy = true) {x y : Nat}
    (typeX : ctx.valueType? x = some (.int ty.width))
    (typeY : ctx.valueType? y = some (.int ty.width))
    {st next : State} {out : V} {tr trace : Array RuleId}
    (empty : st.base.emitted = #[])
    (rhs : (evalExpr program (Stock.sem ctx) {} 999999 rule_lower_1281.rhs (cmpEnv cc x y)).run
      (st,tr) = .ok (some out,next,trace))
    {fr : Clif.Frame} {u v : BitVec ty.width} (dfg : DFGCons ctx fr)
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key)))
    (separatedY : ∀ r,ctx.valueReg? y = some (.vreg r .int) → aliasNum aliases r ≠ st.base.nextVreg) :
    ∃ d code,out = .regsVec [[.vreg d .int]] ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base code ∧
      ∀ world,Runs F isem (code.map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨outTy,Clif.Sem.uextend outTy.width (Clif.Sem.bool8 (Clif.Sem.intcc cc u v))⟩ (ρ' d) ∧
          ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k) := by
  obtain ⟨emitFuel,conditionFuel,outputFuel,condition,middle,emitTrace,value,produced,conditionTrace,
    enoughEmit,enoughCondition,enoughOutput,emitter,conditionCall,outputCall⟩ :=
      actual_root_rhs_calls data_program ctx cc x y rhs
  have outputDemand := stock_apply_demand_mono outputCall
  have conditionHeld : ValuesHeld (Demanded produced) ctx fr (fun key => ρ (aliasNum aliases key)) := by
    apply held.mono
    intro z needed
    have grows := outputDemand z
    unfold Demanded at needed ⊢
    omega
  have execution : CmpExecution F isem aliases cc ty u v st produced value ρ := by
    cases ty
    case i8 =>
      exact stock_cmp_narrow_actual_emitter_values inv false cc rfl dfg getX getY typeX typeY
        enoughEmit enoughCondition emitter conditionCall refines bounded extent conditionHeld separatedY
    case i16 =>
      exact stock_cmp_narrow_actual_emitter_values inv true cc rfl dfg getX getY typeX typeY
        enoughEmit enoughCondition emitter conditionCall refines bounded extent conditionHeld separatedY
    case i32 =>
      exact stock_cmp_wide_actual_emitter_values inv false cc rfl dfg getX getY typeX typeY
        enoughEmit enoughCondition emitter conditionCall refines bounded extent conditionHeld
    case i64 =>
      exact stock_cmp_wide_actual_emitter_values inv true cc rfl dfg getX getY typeX typeY
        enoughEmit enoughCondition emitter conditionCall refines bounded extent conditionHeld
    all_goals simp [eTy] at accepted
  obtain ⟨d,code,result,lower,upper,fragment,executed⟩ := execution
  have width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64 := by
    cases ty <;> simp_all [eTy,Clif.Ty.width]
  have shape := ScalarSelect.stock_select_comparison_condition_shape inv width cc typeX typeY enoughEmit emitter
  obtain ⟨producer,c,chosen,output,finish⟩ := stock_cmp_condition_observed data_program ctx rfl
    enoughCondition shape conditionCall
  have valid := chosen.shape (fun _ _ => ⟨rfl,rfl⟩) shape
  have destination : d = middle.base.nextVreg := by
    have equal := (Reg.vreg.inj (V.reg.inj (result.symm.trans output))).1
    exact equal
  subst d
  have suffix : code = middle.base.emitted.toList ++ [producer,.cset (.vreg middle.base.nextVreg .int) c] := by
    rw [finish] at fragment
    exact ScalarSelect.stock_select_companion_fragment_code empty fragment
  have fresh : aliasNum aliases middle.base.nextVreg = middle.base.nextVreg := by
    apply chaseF_none
    rw [Array.getElem?_eq_none (by omega)]
    rfl
  have lastMapped : (MInst.cset (.vreg middle.base.nextVreg .int) c).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) = .cset (.vreg middle.base.nextVreg .int) c := by
    simp only [MInst.mapRegs,resolve_vreg]
    change MInst.cset (.vreg (aliasNum aliases middle.base.nextVreg) .int) c = _
    rw [fresh]
  rw [result] at outputCall
  obtain ⟨wrapped,state⟩ := stock_cmp_output_observed data_program ctx (by omega) outputCall
  rw [state]
  refine ⟨_,code,wrapped,lower,upper,fragment,?_⟩
  intro world
  apply (executed world).imp
  intro final world' actual values
  constructor
  · have actualSuffix := actual
    rw [suffix,List.map_append] at actualSuffix
    simp only [List.map_cons,List.map_nil,lastMapped] at actualSuffix
    have actualSuffix' : seqRun isem (((middle.base.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ++
      [producer.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))]) ++
      [.cset (.vreg middle.base.nextVreg .int) c]) ρ world = some (.fall final world')  := by
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using actualSuffix
    exact stock_cmp_cset_suffix_extend refines ⟨valid.1,valid.2.1⟩ actualSuffix' values.1 outputAccepted
  · exact values.2
/-- Actual fused execution allocates a result before any scratch-separation
assumption is needed, breaking the availability/separation dependency. -/
theorem stock_cast_cmp_rhs_growth {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cc : Clif.IntCC} {ty : Clif.Ty}
    (accepted : eTy ty = true) {x y : Nat}
    (typeX : ctx.valueType? x = some (.int ty.width))
    (typeY : ctx.valueType? y = some (.int ty.width))
    {st next : State} {out : V} {tr trace : Array RuleId}
    (rhs : (evalExpr program (Stock.sem ctx) {} 999999 rule_lower_1281.rhs (cmpEnv cc x y)).run
      (st,tr) = .ok (some out,next,trace))
    {fr : Clif.Frame} {u v : BitVec ty.width} (dfg : DFGCons ctx fr)
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key)))
    : st.base.nextVreg < next.base.nextVreg := by
  obtain ⟨emitFuel,conditionFuel,outputFuel,condition,middle,emitTrace,value,produced,conditionTrace,
    enoughEmit,enoughCondition,enoughOutput,emitter,conditionCall,outputCall⟩ :=
      actual_root_rhs_calls data_program ctx cc x y rhs
  have outputDemand := stock_apply_demand_mono outputCall
  have conditionHeld : ValuesHeld (Demanded produced) ctx fr (fun key => ρ (aliasNum aliases key)) := by
    apply held.mono
    intro z needed
    have grows := outputDemand z
    unfold Demanded at needed ⊢
    omega
  have growth : st.base.nextVreg < produced.base.nextVreg := by
    cases ty
    case i8 =>
      exact stock_cmp_narrow_actual_emitter_growth inv false cc rfl dfg getX getY typeX typeY
        enoughEmit enoughCondition emitter conditionCall refines bounded extent conditionHeld
    case i16 =>
      exact stock_cmp_narrow_actual_emitter_growth inv true cc rfl dfg getX getY typeX typeY
        enoughEmit enoughCondition emitter conditionCall refines bounded extent conditionHeld
    case i32 =>
      obtain ⟨_,_,_,lower,upper,_,_⟩ := stock_cmp_wide_actual_emitter_values inv false cc rfl
        dfg getX getY typeX typeY enoughEmit enoughCondition emitter conditionCall refines bounded extent conditionHeld
      omega
    case i64 =>
      obtain ⟨_,_,_,lower,upper,_,_⟩ := stock_cmp_wide_actual_emitter_values inv true cc rfl
        dfg getX getY typeX typeY enoughEmit enoughCondition emitter conditionCall refines bounded extent conditionHeld
      omega
    all_goals simp [eTy] at accepted
  have width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64 := by
    cases ty <;> simp_all [eTy,Clif.Ty.width]
  have shape := ScalarSelect.stock_select_comparison_condition_shape inv width cc typeX typeY enoughEmit emitter
  obtain ⟨_,_,_,output,_⟩ := stock_cmp_condition_observed data_program ctx rfl enoughCondition shape conditionCall
  rw [output] at outputCall
  obtain ⟨_,state⟩ := stock_cmp_output_observed data_program ctx (by omega) outputCall
  rw [state]
  exact growth
end Backend.Stock.Proof.ScalarCmp
