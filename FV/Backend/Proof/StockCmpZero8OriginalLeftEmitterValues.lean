module

public import FV.Backend.Proof.StockCmpZeroLeftEmitterSelection
public import FV.Backend.Proof.StockCmpZero8OriginalRhsValues

@[expose] public section

namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
theorem stock_cmp_zero8_original_left_eq_emitter_values 
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {fr : Clif.Frame} {x : Nat} {u : BitVec 8} (get : fr.getAs x .i8 = .ok u)
    (typed : ctx.valueType? x = some (.int 8)) 
    {y j : Nat} {info : IInfo} {i : Int}
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int i]) (normalized : u64 i = 0)
    {st middle next : State} {tr inverseTrace conditionStart trace : Array RuleId}
    {emitFuel fuel : Nat} {condition out : V} (enoughEmit : 240 ≤ emitFuel) (enoughCondition : 119 ≤ fuel)
    (emitter : ApplyInternal program (Stock.sem ctx) {} emitFuel 123 652
      [.data 145 (ccIdx .eq) [],.value y,.value x] (st,tr) condition (middle,inverseTrace))
    (conditionCall : ApplyInternal program (Stock.sem ctx) {} fuel 27 715 [condition]
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
  obtain ⟨rhsTrace,rhs,traceEq⟩ := stock_cmp_zero_left_emitter_selected data_program ctx false
    (by omega) defined found data normalized emitter
  obtain ⟨n,fuelEq⟩ : ∃ n,emitFuel=n+240 := ⟨emitFuel-240,by omega⟩
  simp only [Bool.false_eq_true,ite_false] at rhs
  rw [fuelEq] at rhs
  exact stock_cmp_zero8_original_eq_rhs_values inv get typed enoughCondition rhs
    conditionCall refines bounded extent held

theorem stock_cmp_zero8_original_left_ne_emitter_values 
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {fr : Clif.Frame} {x : Nat} {u : BitVec 8} (get : fr.getAs x .i8 = .ok u)
    (typed : ctx.valueType? x = some (.int 8)) 
    {y j : Nat} {info : IInfo} {i : Int}
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int i]) (normalized : u64 i = 0)
    {st middle next : State} {tr emitterTrace conditionStart trace : Array RuleId}
    {emitFuel fuel : Nat} {condition out : V} (enoughEmit : 240 ≤ emitFuel) (enoughCondition : 119 ≤ fuel)
    (emitter : ApplyInternal program (Stock.sem ctx) {} emitFuel 123 652
      [.data 145 (ccIdx .ne) [],.value y,.value x] (st,tr) condition (middle,emitterTrace))
    (conditionCall : ApplyInternal program (Stock.sem ctx) {} fuel 27 715 [condition]
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
  obtain ⟨rhsTrace,rhs,traceEq⟩ := stock_cmp_zero_left_emitter_selected data_program ctx true
    (by omega) defined found data normalized emitter
  obtain ⟨n,fuelEq⟩ : ∃ n,emitFuel=n+240 := ⟨emitFuel-240,by omega⟩
  simp only [ite_true] at rhs
  rw [fuelEq] at rhs
  exact stock_cmp_zero8_original_ne_rhs_values inv get typed enoughCondition rhs
    conditionCall refines bounded extent held
end Backend.Stock.Proof.ScalarCmp
