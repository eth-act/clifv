import FV.Backend.Proof.StockSelectNonzeroActualValues
import FV.Backend.Proof.StockSelectNonzeroAllocation
import FV.Backend.Proof.StockSelectConditionCalls
import FV.Backend.Proof.StockSelectOriginalSourceMatch
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
/-- The actual650 source dispatch derives the real651 call when its original
condition is a parameter. Comparison look-through is excluded by the original
DFG definition query, rather than a machine-value certificate. -/
theorem stock_original_select_parameter_condition_calls {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {c fuel : Nat} (enough : 400 ≤ fuel)
    (parameter : ctx.defInst? c = none) {st middle : State} {tr trace : Array RuleId} {condition : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 123 650 [.value c] (st,tr) condition (middle,trace)) :
    ∃ helperFuel helperTrace,300 ≤ helperFuel ∧
      ApplyInternal program (Stock.sem ctx) {} helperFuel 123 651 [.value c] (st,tr) condition (middle,helperTrace) := by
  rcases stock_original_select_condition_calls inv enough run with ordinary | ⟨cc,ty,a,b,origin,_⟩
  · exact ordinary
  · have absent : ctx.defClif? c = none := by simp [Ctx.defClif?,parameter]
    rcases origin with direct | ⟨_,_,extended,_⟩
    · rw [absent] at direct; cases direct
    · rw [absent] at extended; cases extended
/-- Real selected-root allocation is established before source-value transfer.
This parameter-condition variant leaves comparison look-through to its own
source-provenance branch and adds no checker/input restriction. -/
theorem stock_original_select_parameter_selected_allocation {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cty ty : Clif.Ty}
    (conditionWidth : cty.width = 8 ∨ cty.width = 16 ∨ cty.width = 32 ∨ cty.width = 64)
    {i c x y : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.select ty c x y))
    (typed : ctx.valueType? c = some (.int cty.width)) (parameter : ctx.defInst? c = none)
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules) :
    ∃ d,out = .regsVec [[.vreg d .int]] ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      next.base.nextVreg = st.base.nextVreg+(if cty = .i16 then 2 else 1) := by
  obtain ⟨_,_,_,_,emitFuel,selectFuel,condition,middle,emitTrace,value,produced,selectTrace,
    enoughEmit,enoughSelect,emitter,consumer,output⟩ := stock_original_select_selected_calls inv source clif selected
  obtain ⟨helperFuel,helperTrace,enough,nonzero⟩ := stock_original_select_parameter_condition_calls inv enoughEmit parameter emitter
  have allocation := stock_select_nonzero_actual_allocation inv conditionWidth (stock_original_select_source_data inv source clif).1
    typed (by omega) enoughSelect nonzero consumer
  obtain ⟨valueEq,lower,frontier,upper⟩ := allocation
  rw [valueEq,stock_ctor_baseOnly ctx T.output _ produced (by decide)] at output
  change ExtResult.ok (.regsVec [[.vreg middle.base.nextVreg .int]],produced) = .ok (out,next) at output
  have both := Prod.mk.inj (ExtResult.ok.inj output)
  rw [← both.2]
  exact ⟨middle.base.nextVreg,both.1.symm,lower,by omega,frontier⟩
/-- Actual selected original select with a parameter condition computes the
original chosen value and full fresh-write frame. Its retained caller derives
source separation from original availability before invoking this theorem. -/
theorem stock_original_select_parameter_selected_source_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cty ty : Clif.Ty}
    (conditionWidth : cty.width = 8 ∨ cty.width = 16 ∨ cty.width = 32 ∨ cty.width = 64)
    {i c x y : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.select ty c x y))
    (typed : ctx.valueType? c = some (.int cty.width)) (parameter : ctx.defInst? c = none)
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {test : BitVec cty.width} {u v : BitVec ty.width}
    (getC : fr.getAs c cty = .ok test) (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key)))
    (empty : st.base.emitted = #[])
    (outsideX : ∀ key,ctx.valueReg? x = some (.vreg key .int) →
      aliasNum aliases key < st.base.nextVreg ∨ next.base.nextVreg ≤ aliasNum aliases key)
    (outsideY : ∀ key,ctx.valueReg? y = some (.vreg key .int) →
      aliasNum aliases key < st.base.nextVreg ∨ next.base.nextVreg ≤ aliasNum aliases key) :
    ∃ d code,out = .regsVec [[.vreg d .int]] ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base code ∧
      ∀ world,Runs F isem (code.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world
        (fun final _ => VHolds ⟨ty,Clif.Sem.select test u v⟩ (final d) ∧
          ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → final k = ρ k) := by
  obtain ⟨_,_,_,_,emitFuel,selectFuel,condition,middle,emitTrace,value,produced,selectTrace,
    enoughEmit,enoughSelect,emitter,consumer,output⟩ := stock_original_select_selected_calls inv source clif selected
  obtain ⟨helperFuel,helperTrace,enough,nonzero⟩ := stock_original_select_parameter_condition_calls inv enoughEmit parameter emitter
  have width := (stock_original_select_source_data inv source clif).1
  obtain ⟨valueEq,_,_,_⟩ := stock_select_nonzero_actual_allocation inv conditionWidth width typed (by omega) enoughSelect nonzero consumer
  rw [valueEq,stock_ctor_baseOnly ctx T.output _ produced (by decide)] at output
  change ExtResult.ok (.regsVec [[.vreg middle.base.nextVreg .int]],produced) = .ok (out,next) at output
  have both := Prod.mk.inj (ExtResult.ok.inj output)
  have sameState : next = produced := both.2.symm
  rw [sameState] at held outsideX outsideY ⊢
  obtain ⟨d,code,actualOutput,lower,upper,fragment,execution⟩ := stock_select_nonzero_actual_source_values inv conditionWidth width dfg
    getC getX getY typed (by omega) enoughSelect empty nonzero consumer refines bounded extent held outsideX outsideY
  have sameD : d = middle.base.nextVreg := by exact (Reg.vreg.inj (List.cons.inj (V.regs.inj (actualOutput.symm.trans valueEq))).1).1
  subst d
  exact ⟨middle.base.nextVreg,code,both.1.symm,lower,upper,fragment,execution⟩
end Backend.Stock.Proof.ScalarSelect
