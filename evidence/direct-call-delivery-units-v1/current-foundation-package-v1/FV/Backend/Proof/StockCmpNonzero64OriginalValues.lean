import FV.Backend.Proof.StockCmpZeroHelpers
import FV.Backend.Proof.StockCmpNonzero64OriginalSelection
import FV.Backend.Proof.StockCmpConditionValues
import FV.Backend.Proof.StockDemandMono
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual nonzero selection and condition execution hold the original64-bit
source predicate through final aliases, deriving requests, code and frame internally. -/
theorem stock_cmp_original_nonzero64_values 
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {fr : Clif.Frame} {x : Nat} {u : BitVec 64} (get : fr.getAs x .i64 = .ok u)
    (typed : ctx.valueType? x = some (.int 64)) 
    {st middle next : State} {tr emitterTrace conditionStart trace : Array RuleId}
    {emitFuel fuel : Nat} {condition out : V} (enoughEmit : 200 ≤ emitFuel) (enoughCondition : 119 ≤ fuel)
    (emitter : ApplyInternal program (Stock.sem ctx) {} emitFuel 123 651 [.value x]
      (st,tr) condition (middle,emitterTrace))
    (conditionCall : ApplyInternal program (Stock.sem ctx) {} fuel 27 715 [condition]
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
  obtain ⟨rhsTrace,rhs,_⟩ := stock_cmp_original_nonzero64_selected ctx inv enoughEmit typed emitter
  obtain ⟨n,gas⟩ : ∃ n,emitFuel=n+30 := ⟨emitFuel-30,by omega⟩
  rw [gas] at rhs
  obtain ⟨safe,rx,mapped,producer,finish⟩ := stock_cmp_nonzero64_rhs_observed data_program ctx rfl rhs
  obtain ⟨key,rfl⟩ := inv.valueReg x rx mapped
  have needed : Demanded next x := by
    have marked := (mark_demand st x (extent x _ mapped)).1
    have grows := stock_apply_demand_mono conditionCall x
    rw [finish] at grows
    unfold Demanded
    omega
  have input := held.read needed (getAs_ok get) mapped
  have word : opnd .size64 (ρ (aliasNum aliases key)) = u := by
    change (ρ (aliasNum aliases key)).setWidth 64 = u at input
    simpa only [opnd,OperandSize.bits,lo64,BitVec.setWidth_eq] using input
  rw [producer] at conditionCall
  have boundedMiddle : aliases.size ≤ middle.base.nextVreg := by rw [finish]; exact bounded
  obtain ⟨d,output,lower,upper,fragment,execution⟩ := stock_cmp_zero_condition_values data_program ctx rfl enoughCondition true .size64 rfl
    conditionCall refines boundedMiddle
  simp only [ite_true] at execution fragment
  rw [word] at execution
  refine ⟨key,d,mapped,output,?_,upper,?_,execution⟩
  · rw [finish] at lower; exact lower
  · rw [finish] at fragment; exact fragment
/-- Actual nonzero selection, inversion and condition execution hold the original64-bit
source equality-to-zero predicate through final aliases, deriving requests, code and frame internally. -/
theorem stock_cmp_original_equal_zero64_values 
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {fr : Clif.Frame} {x : Nat} {u : BitVec 64} (get : fr.getAs x .i64 = .ok u)
    (typed : ctx.valueType? x = some (.int 64)) 
    {st produced middle next : State} {tr emitterTrace inverseStart inverseTrace conditionStart trace : Array RuleId}
    {emitFuel inverseFuel fuel : Nat} {raw condition out : V} (enoughEmit : 200 ≤ emitFuel) (enoughCondition : 119 ≤ fuel) (enoughInverse : 39 ≤ inverseFuel)
    (emitter : ApplyInternal program (Stock.sem ctx) {} emitFuel 123 651 [.value x]
      (st,tr) raw (produced,emitterTrace))
    (inversion : ApplyInternal program (Stock.sem ctx) {} inverseFuel 123 649 [raw]
      (produced,inverseStart) condition (middle,inverseTrace))
    (conditionCall : ApplyInternal program (Stock.sem ctx) {} fuel 27 715 [condition]
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
  obtain ⟨rhsTrace,rhs,_⟩ := stock_cmp_original_nonzero64_selected ctx inv enoughEmit typed emitter
  obtain ⟨n,gas⟩ : ∃ n,emitFuel=n+30 := ⟨emitFuel-30,by omega⟩
  rw [gas] at rhs
  obtain ⟨safe,rx,mapped,producer,finish⟩ := stock_cmp_nonzero64_rhs_observed data_program ctx rfl rhs
  obtain ⟨key,rfl⟩ := inv.valueReg x rx mapped
  rw [producer] at inversion
  obtain ⟨inverted,unchanged⟩ := stock_cmp_zero_invert_observed data_program ctx enoughInverse true (.vreg key .int) (.data 93 1 []) inversion
  have full : middle = st.mark x := unchanged.trans finish
  have needed : Demanded next x := by
    have marked := (mark_demand st x (extent x _ mapped)).1
    have grows := stock_apply_demand_mono conditionCall x
    rw [full] at grows
    unfold Demanded
    omega
  have input := held.read needed (getAs_ok get) mapped
  have word : opnd .size64 (ρ (aliasNum aliases key)) = u := by
    change (ρ (aliasNum aliases key)).setWidth 64 = u at input
    simpa only [opnd,OperandSize.bits,lo64,BitVec.setWidth_eq] using input
  rw [inverted] at conditionCall
  have boundedMiddle : aliases.size ≤ middle.base.nextVreg := by rw [full]; exact bounded
  obtain ⟨d,output,lower,upper,fragment,execution⟩ := stock_cmp_zero_condition_values data_program ctx rfl enoughCondition false .size64 rfl
    conditionCall refines boundedMiddle
  simp only [Bool.false_eq_true,ite_false] at execution fragment
  rw [word] at execution
  refine ⟨key,d,mapped,output,?_,upper,?_,execution⟩
  · rw [full] at lower; exact lower
  · rw [full] at fragment; exact fragment
end Backend.Stock.Proof.ScalarCmp
