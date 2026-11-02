import FV.Backend.Proof.StockCmpNonconstantValues
import FV.Backend.Proof.StockCmpSelectedCalls
import FV.Backend.Proof.StockCmpOutput
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual original first-match comparison selection derives its emitter,
condition and output executions and holds the original32/64 nonconstant result.
No caller-selected root, RHS, producer, output or helper certificate is needed. -/
theorem stock_cmp_nonconstant_selected_source_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cc : Clif.IntCC} {ty : Clif.Ty}
    (width : ty.width = 32 ∨ ty.width = 64) {i x y : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.icmp cc ty x y))
    (typeX : ctx.valueType? x = some (.int (szOf ty.width).bits))
    (typeY : ctx.valueType? y = some (.int (szOf ty.width).bits))
    (notConstantX : NonConstantSource ctx x) (notConstantY : NonConstantSource ctx y)
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx i st out next rules)
    {fr : Clif.Frame} {u v : BitVec ty.width} (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ nx ny d,ctx.valueReg? x = some (.vreg nx .int) ∧ ctx.valueReg? y = some (.vreg ny .int) ∧
      out = .regsVec [[.vreg d .int]] ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [.aluRRR .subS (szOf ty.width) .xzr (.vreg nx .int) (.vreg ny .int),
        .cset (.vreg d .int) (condOf cc)] ∧
      ∀ world,Runs F isem ([MInst.aluRRR .subS (szOf ty.width) .xzr (.vreg nx .int) (.vreg ny .int),
        .cset (.vreg d .int) (condOf cc)].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc cc u v)⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = ρ k) := by
  obtain ⟨_,_,_,_,_,calls⟩ := stock_cmp_selected_calls inv source clif selected
  obtain ⟨emitFuel,conditionFuel,outputFuel,condition,middle,emitTrace,value,produced,conditionTrace,
    enoughEmit,enoughCondition,enoughOutput,emitter,conditionCall,outputCall⟩ := calls
  have outputDemand := stock_apply_demand_mono outputCall
  have conditionHeld : ValuesHeld (Demanded produced) ctx fr (fun key => ρ (aliasNum aliases key)) := by
    apply held.mono
    intro z needed
    have grows := outputDemand z
    unfold Demanded at needed ⊢
    omega
  obtain ⟨nx,ny,d,mapX,mapY,result,lower,upper,fragment,execution⟩ := stock_cmp_nonconstant_emitter_source_values
    data_program inv cc width getX getY typeX typeY notConstantX notConstantY enoughEmit enoughCondition
    emitter conditionCall refines bounded extent conditionHeld
  rw [result] at outputCall
  obtain ⟨output,state⟩ := stock_cmp_output_observed data_program ctx enoughOutput outputCall
  rw [state]
  exact ⟨nx,ny,d,mapX,mapY,output,lower,upper,fragment,execution⟩
end Backend.Stock.Proof.ScalarCmp
