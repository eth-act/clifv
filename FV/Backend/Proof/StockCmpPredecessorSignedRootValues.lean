module

public import FV.Backend.Proof.StockCmpPredecessorSignedEmitterValues
public import FV.Backend.Proof.StockCmpSelectedCalls
public import FV.Backend.Proof.StockCmpOutput

@[expose] public section

namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual original first-match comparison selection derives its emitter,
condition and output executions and holds the original32/64 immediate constant result.
No caller-selected root, RHS, producer, output or helper certificate is needed. -/
theorem stock_cmp_predecessor_signed_selected_source_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {ty : Clif.Ty}
    (width : ty.width = 32 ∨ ty.width = 64) {i x y : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.icmp .sge ty x y))
    (typeX : ctx.valueType? x = some (.int (szOf ty.width).bits))
    {j : Nat} {constantInfo : IInfo} {literal : Int} {imm : Imm12}
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some constantInfo)
    (data : constantInfo.data = .data 152 35 [.data 151 57 [],.int literal])
    (odd : u64 literal % 2 = 1) (encoded : Imm12.ofNat? (u64 (literal-1)) = some imm)
    (nonencodable : Imm12.ofNat? (u64 literal) = none)
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx i st out next rules)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {u v : BitVec ty.width} (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ nx d,ctx.valueReg? x = some (.vreg nx .int) ∧
      out = .regsVec [[.vreg d .int]] ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [.aluRRImm12 .subS (szOf ty.width) .xzr (.vreg nx .int) imm,
        .cset (.vreg d .int) (condOf .sgt)] ∧
      ∀ world,Runs F isem ([MInst.aluRRImm12 .subS (szOf ty.width) .xzr (.vreg nx .int) imm,
        .cset (.vreg d .int) (condOf .sgt)].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc .sge u v)⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = ρ k) := by
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
  obtain ⟨nx,d,mapX,result,lower,upper,fragment,execution⟩ := stock_cmp_predecessor_signed_emitter_source_values
    data_program inv width dfg getX getY defined found data encoded odd nonencodable typeX enoughEmit enoughCondition
    emitter conditionCall refines bounded extent conditionHeld
  rw [result] at outputCall
  obtain ⟨output,state⟩ := stock_cmp_output_observed data_program ctx enoughOutput outputCall
  rw [state]
  exact ⟨nx,d,mapX,output,lower,upper,fragment,execution⟩
end Backend.Stock.Proof.ScalarCmp
