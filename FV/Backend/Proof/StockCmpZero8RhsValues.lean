import FV.Backend.Proof.StockCmpZero32RuleCalls
import FV.Backend.Proof.StockCmpNonzero8SelectedValues
import FV.Backend.Proof.StockCmpEqualZero8Values
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual inequality rule RHS and condition execution yield the original source predicate. -/
theorem stock_cmp_zero8_ne_rhs_values {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {fr : Clif.Frame} {x : Nat} {u : BitVec 8} (get : fr.getAs x .i8 = .ok u)
    (typed : ctx.valueType? x = some (.int 8)) (parameter : ctx.defInst? x = none)
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
    ∃ key d,ctx.valueReg? x = some (.vreg key .int) ∧ out = .reg (.vreg d .int) ∧
      st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [MInst.aluRRImmLogic .andS .size32 .xzr (.vreg key .int) ⟨255,.size32⟩,.cset (.vreg d .int) .ne] ∧
      ∀ world,Runs F isem ([MInst.aluRRImmLogic .andS .size32 .xzr (.vreg key .int) ⟨255,.size32⟩,.cset (.vreg d .int) .ne].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (u != 0)⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = ρ k) := by
  obtain ⟨emitFuel,enoughEmit,emitter⟩ := stock_cmp_zero32_ne_rhs_calls hp ctx x n rhs
  exact stock_cmp_parameter_nonzero8_values hp inv get typed parameter (by omega) enoughCondition
    emitter conditionCall refines bounded extent held
/-- Actual equality rule RHS derives inversion internally and yields the original source predicate. -/
theorem stock_cmp_zero8_eq_rhs_values {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {fr : Clif.Frame} {x : Nat} {u : BitVec 8} (get : fr.getAs x .i8 = .ok u)
    (typed : ctx.valueType? x = some (.int 8)) (parameter : ctx.defInst? x = none)
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
    ∃ key d,ctx.valueReg? x = some (.vreg key .int) ∧ out = .reg (.vreg d .int) ∧
      st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [MInst.aluRRImmLogic .andS .size32 .xzr (.vreg key .int) ⟨255,.size32⟩,.cset (.vreg d .int) .eq] ∧
      ∀ world,Runs F isem ([MInst.aluRRImmLogic .andS .size32 .xzr (.vreg key .int) ⟨255,.size32⟩,.cset (.vreg d .int) .eq].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (u == 0)⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = ρ k) := by
  obtain ⟨emitFuel,inverseFuel,raw,produced,emitterTrace,enoughEmit,enoughInverse,emitter,inversion⟩ :=
    stock_cmp_zero32_eq_rhs_calls hp ctx x n rhs
  obtain ⟨rhsTrace,sourceRhs,sourceTrace⟩ := stock_cmp_parameter_nonzero8_selected hp ctx (by omega) typed parameter emitter
  obtain ⟨m,gas⟩ : ∃ m,emitFuel=m+100 := ⟨emitFuel-100,by omega⟩
  rw [gas] at sourceRhs
  exact stock_cmp_equal_zero8_rhs_source_values hp inv get typed enoughCondition enoughInverse
    sourceRhs inversion conditionCall refines bounded extent held

end Backend.Stock.Proof.ScalarCmp
