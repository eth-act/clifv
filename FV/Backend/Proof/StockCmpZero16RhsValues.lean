import FV.Backend.Proof.StockCmpZero32RuleCalls
import FV.Backend.Proof.StockCmpNonzero16Values
import FV.Backend.Proof.StockCmpNonzero16Selection
import FV.Backend.Proof.StockCmpEqualZero16Values
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual inequality rule RHS and condition execution yield the original source predicate. -/
theorem stock_cmp_zero16_ne_rhs_values {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {x : Nat} {u : BitVec 16} (get : fr.getAs x .i16 = .ok u)
    (typed : ctx.valueType? x = some (.int 16)) (parameter : ctx.defInst? x = none)
    {st middle next : State} {tr emitterTrace conditionStart trace : Array RuleId}
    {n fuel : Nat} {condition out : V} (enoughCondition : 119 ≤ fuel)
    (rhs : (evalExpr p (Stock.sem ctx) {} (n+240) rule_inst_5172.rhs
      #[some (.value x)]).run (st,tr) = .ok (some condition,middle,emitterTrace))
    (conditionCall : ApplyInternal p (Stock.sem ctx) {} fuel 27 715 [condition]
      (middle,conditionStart) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ ms r d,out = .reg (.vreg d .int) ∧
      st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base (ms ++ [cmpImm0 .size32 r,.cset (.vreg d .int) .ne]) ∧
      ∀ world,Runs F isem ((ms ++ [cmpImm0 .size32 r,.cset (.vreg d .int) .ne]).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (u != 0)⟩ (ρ' d) ∧ ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k) := by
  obtain ⟨emitFuel,enoughEmit,emitter⟩ := stock_cmp_zero32_ne_rhs_calls hp ctx x n rhs
  obtain ⟨rhsTrace,sourceRhs,sourceTrace⟩ := stock_cmp_parameter_nonzero16_selected hp ctx (by omega) typed parameter emitter
  obtain ⟨m,gas⟩ : ∃ m,emitFuel=m+220 := ⟨emitFuel-220,by omega⟩
  rw [gas] at sourceRhs
  exact stock_cmp_nonzero16_rhs_source_values hp inv dfg get enoughCondition sourceRhs conditionCall refines bounded extent held
/-- Actual equality rule RHS derives inversion internally and yields the original source predicate. -/
theorem stock_cmp_zero16_eq_rhs_values {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {x : Nat} {u : BitVec 16} (get : fr.getAs x .i16 = .ok u)
    (typed : ctx.valueType? x = some (.int 16)) (parameter : ctx.defInst? x = none)
    {st middle next : State} {tr inverseTrace conditionStart trace : Array RuleId}
    {n fuel : Nat} {condition out : V} (enoughCondition : 119 ≤ fuel)
    (rhs : (evalExpr p (Stock.sem ctx) {} (n+240) rule_inst_5170.rhs
      #[some (.value x)]).run (st,tr) = .ok (some condition,middle,inverseTrace))
    (conditionCall : ApplyInternal p (Stock.sem ctx) {} fuel 27 715 [condition]
      (middle,conditionStart) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ ms r d,out = .reg (.vreg d .int) ∧
      st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base (ms ++ [cmpImm0 .size32 r,.cset (.vreg d .int) .eq]) ∧
      ∀ world,Runs F isem ((ms ++ [cmpImm0 .size32 r,.cset (.vreg d .int) .eq]).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (u == 0)⟩ (ρ' d) ∧ ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k) := by
  obtain ⟨emitFuel,inverseFuel,raw,produced,emitterTrace,enoughEmit,enoughInverse,emitter,inversion⟩ :=
    stock_cmp_zero32_eq_rhs_calls hp ctx x n rhs
  obtain ⟨rhsTrace,sourceRhs,sourceTrace⟩ := stock_cmp_parameter_nonzero16_selected hp ctx (by omega) typed parameter emitter
  obtain ⟨m,gas⟩ : ∃ m,emitFuel=m+220 := ⟨emitFuel-220,by omega⟩
  rw [gas] at sourceRhs
  exact stock_cmp_equal_zero16_rhs_source_values hp inv dfg get enoughCondition enoughInverse sourceRhs inversion conditionCall refines bounded extent held
end Backend.Stock.Proof.ScalarCmp
