import FV.Backend.Proof.StockCmpZeroValues
import FV.Backend.Proof.StockCmpZeroRuleCalls
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual inequality rule RHS and condition execution yield the original source predicate. -/
theorem stock_cmp_zero_ne_rhs_values {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {fr : Clif.Frame} {x : Nat} {u : BitVec 64} (get : fr.getAs x .i64 = .ok u)
    (typed : ctx.valueType? x = some (.int 64)) (parameter : ctx.defInst? x = none)
    {st middle next : State} {tr emitterTrace conditionStart trace : Array RuleId}
    {n fuel : Nat} {condition out : V} (enoughCondition : 119 ≤ fuel)
    (rhs : (evalExpr p (Stock.sem ctx) {} (n+220) rule_inst_5172.rhs
      #[some (.value x)]).run (st,tr) = .ok (some condition,middle,emitterTrace))
    (conditionCall : ApplyInternal p (Stock.sem ctx) {} fuel 27 715 [condition]
      (middle,conditionStart) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ key d,ctx.valueReg? x = some (.vreg key .int) ∧ out = .reg (.vreg d .int) ∧
      st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [cmpImm0 .size64 key,.cset (.vreg d .int) .ne] ∧
      ∀ world,Runs F isem ([cmpImm0 .size64 key,.cset (.vreg d .int) .ne].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (u != 0)⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = ρ k) := by
  obtain ⟨emitFuel,enoughEmit,emitter⟩ := stock_cmp_zero_ne_rhs_calls hp ctx x n rhs
  exact stock_cmp_parameter_nonzero64_values hp inv get typed parameter enoughEmit enoughCondition
    emitter conditionCall refines bounded extent held
/-- Actual equality rule RHS derives inversion internally and yields the original source predicate. -/
theorem stock_cmp_zero_eq_rhs_values {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {fr : Clif.Frame} {x : Nat} {u : BitVec 64} (get : fr.getAs x .i64 = .ok u)
    (typed : ctx.valueType? x = some (.int 64)) (parameter : ctx.defInst? x = none)
    {st middle next : State} {tr inverseTrace conditionStart trace : Array RuleId}
    {n fuel : Nat} {condition out : V} (enoughCondition : 119 ≤ fuel)
    (rhs : (evalExpr p (Stock.sem ctx) {} (n+220) rule_inst_5170.rhs
      #[some (.value x)]).run (st,tr) = .ok (some condition,middle,inverseTrace))
    (conditionCall : ApplyInternal p (Stock.sem ctx) {} fuel 27 715 [condition]
      (middle,conditionStart) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ key d,ctx.valueReg? x = some (.vreg key .int) ∧ out = .reg (.vreg d .int) ∧
      st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [cmpImm0 .size64 key,.cset (.vreg d .int) .eq] ∧
      ∀ world,Runs F isem ([cmpImm0 .size64 key,.cset (.vreg d .int) .eq].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (u == 0)⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = ρ k) := by
  obtain ⟨emitFuel,inverseFuel,raw,produced,emitterTrace,enoughEmit,enoughInverse,emitter,inversion⟩ :=
    stock_cmp_zero_eq_rhs_calls hp ctx x n rhs
  exact stock_cmp_parameter_equal_zero64_values hp inv get typed parameter enoughEmit enoughCondition
    enoughInverse emitter inversion conditionCall refines bounded extent held
end Backend.Stock.Proof.ScalarCmp
