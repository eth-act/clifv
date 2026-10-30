import FV.Backend.Proof.StockCmpZero8OriginalLeftEmitterValues
import FV.Backend.Proof.StockCmpSelectedCalls
import FV.Backend.Proof.StockCmpOutput
import FV.Backend.Proof.StockDivConstantSource
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private def ZeroRootCalls (ctx : Ctx) (cc : Clif.IntCC) (x y : Nat)
    (st next : State) (tr trace : Array RuleId) (out : V) : Prop :=
  ∃ condition middle emitTrace value produced conditionTrace,
    ApplyInternal program (Stock.sem ctx) {} 999993 123 652 [.data 145 (ccIdx cc) [],.value x,.value y]
      (st,tr) condition (middle,emitTrace) ∧
    ApplyInternal program (Stock.sem ctx) {} 999995 27 715 [condition]
      (middle,emitTrace) value (produced,conditionTrace) ∧
    ApplyInternal program (Stock.sem ctx) {} 999997 25 172 [value]
      (produced,conditionTrace) out (next,trace)
attribute [local irreducible] ZeroRootCalls
private theorem root_calls (ctx : Ctx) (cc : Clif.IntCC) (x y : Nat)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr program (Stock.sem ctx) {} 999999 rule_lower_2215.rhs (cmpEnv cc x y)).run
      (st,tr) = .ok (some out,next,trace)) : ZeroRootCalls ctx cc x y st next tr trace out := by
  have hp := data_program
  cases hp
  isel_inv [*,rule_lower_2215,cmpEnv,env3] at run
  isel_destruct
  subst_vars
  rename_i value produced condition middle outputCall conditionCall emitCall
  unfold ZeroRootCalls
  exact ⟨condition,middle.1,middle.2,value,produced.1,produced.2,emitCall,conditionCall,outputCall⟩
/-- Original successful comparison selection derives the zero-rule helper chain,
output wrapper and source bool8 value internally, under the original DFG relation. -/
theorem stock_cmp_zero8_original_left_selected_source_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (nonzero : Bool) {i x y : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.icmp (if nonzero then .ne else .eq) .i8 y x))
    (typeX : ctx.valueType? x = some (.int 8)) 
    {j : Nat} {constantInfo : IInfo} {literal : Int}
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some constantInfo)
    (data : constantInfo.data = .data 152 35 [.data 151 57 [],.int literal]) (normalized : u64 literal = 0)
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx i st out next rules)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {u v : BitVec 8}
    (getX : fr.getAs x .i8 = .ok u) (getY : fr.getAs y .i8 = .ok v)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ nx d,ctx.valueReg? x = some (.vreg nx .int) ∧
      out = .regsVec [[.vreg d .int]] ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [MInst.aluRRImmLogic .andS .size32 .xzr (.vreg nx .int) ⟨255,.size32⟩,.cset (.vreg d .int) (if nonzero then .ne else .eq)] ∧
      ∀ world,Runs F isem ([MInst.aluRRImmLogic .andS .size32 .xzr (.vreg nx .int) ⟨255,.size32⟩,.cset (.vreg d .int) (if nonzero then .ne else .eq)].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc (if nonzero then .ne else .eq) v u)⟩ (ρ' d) ∧
          ∀ k,k ≠ d → ρ' k = ρ k) := by
  obtain ⟨_,chosen,envEq,stateEq,traceEq,_⟩ := stock_cmp_selected_calls inv source clif selected
  have rhs := selected.rhsRun
  rw [chosen,envEq,stateEq,traceEq] at rhs
  have calls := root_calls ctx (if nonzero then .ne else .eq) y x rhs
  unfold ZeroRootCalls at calls
  obtain ⟨condition,middle,emitTrace,value,produced,conditionTrace,emitter,conditionCall,outputCall⟩ := calls
  have constant := (ScalarDiv.stock_div_constant_source_value inv dfg getY defined found data).2
  have literalValue : u64 literal = v.toNat := by
    rw [constant]
    exact u64_imm64OfIconst (ty := .i8) (c := v) (by decide)
  have zeroValue : v = 0 := by
    apply BitVec.eq_of_toNat_eq
    exact literalValue.symm.trans normalized
  subst v
  have conditionHeld : ValuesHeld (Demanded produced) ctx fr (fun key => ρ (aliasNum aliases key)) := by
    apply held.mono
    intro z needed
    have grows := stock_apply_demand_mono outputCall z
    unfold Demanded at needed ⊢
    omega
  cases nonzero
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true] at *
  · obtain ⟨nx,d,mapX,result,lower,upper,fragment,execution⟩ := stock_cmp_zero8_original_left_eq_emitter_values
      inv getX typeX defined found data normalized (by decide) (by decide)
      emitter conditionCall refines bounded extent conditionHeld
    rw [result] at outputCall
    obtain ⟨output,state⟩ := stock_cmp_output_observed data_program ctx (by decide) outputCall
    rw [state]
    refine ⟨nx,d,mapX,output,lower,upper,fragment,?_⟩
    simpa [Clif.Sem.intcc,bne,Bool.beq_comm] using execution
  · obtain ⟨nx,d,mapX,result,lower,upper,fragment,execution⟩ := stock_cmp_zero8_original_left_ne_emitter_values
      inv getX typeX defined found data normalized (by decide) (by decide)
      emitter conditionCall refines bounded extent conditionHeld
    rw [result] at outputCall
    obtain ⟨output,state⟩ := stock_cmp_output_observed data_program ctx (by decide) outputCall
    rw [state]
    refine ⟨nx,d,mapX,output,lower,upper,fragment,?_⟩
    simpa [Clif.Sem.intcc,bne,Bool.beq_comm] using execution
end Backend.Stock.Proof.ScalarCmp
