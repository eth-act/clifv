import FV.Backend.Proof.StockCmpNonzero8Values
import FV.Backend.Proof.StockCmpNonzero8Selection
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
theorem stock_cmp_parameter_nonzero8_values {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {fr : Clif.Frame} {x : Nat} {u : BitVec 8} (get : fr.getAs x .i8 = .ok u)
    (typed : ctx.valueType? x = some (.int 8)) (parameter : ctx.defInst? x = none)
    {st middle next : State} {tr emitterTrace conditionStart trace : Array RuleId}
    {emitFuel fuel : Nat} {condition out : V} (enoughEmit : 200 ≤ emitFuel) (enoughCondition : 119 ≤ fuel)
    (emitter : ApplyInternal p (Stock.sem ctx) {} emitFuel 123 651 [.value x]
      (st,tr) condition (middle,emitterTrace))
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
  obtain ⟨rhsTrace,rhs,traceEq⟩ := stock_cmp_parameter_nonzero8_selected hp ctx enoughEmit typed parameter emitter
  obtain ⟨n,fuelEq⟩ : ∃ n,emitFuel=n+100 := ⟨emitFuel-100,by omega⟩
  rw [fuelEq] at rhs
  exact stock_cmp_nonzero8_rhs_source_values hp inv get typed enoughCondition rhs conditionCall
    refines bounded extent held
end Backend.Stock.Proof.ScalarCmp
