import FV.Backend.Proof.StockCmpNarrowConstantSelection
import FV.Backend.Proof.StockCmpNarrowRhsObserved
import FV.Backend.Proof.StockCmpSelectedCalls
import FV.Backend.Proof.StockCmpOutput
import FV.Backend.Proof.StockCmpCondition
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Real original narrow comparison selection allocates exactly its extension
scratch and boolean result. This structural fact requires no machine-value or
scratch-separation premise and breaks the availability/value dependency. -/
theorem stock_cmp_narrow_constant_selected_allocation {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cc : Clif.IntCC} (half : Bool) {ty : Clif.Ty} {i x y : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.icmp cc ty x y))
    (typeX : ctx.valueType? x = some (.int (if half then 16 else 8)))
    (typeY : ctx.valueType? y = some (.int (if half then 16 else 8)))
    (notConstantX : NonConstantSource ctx x) {constantJ : Nat} {constantInfo : IInfo} {literal : Int}
    (defined : ctx.defInst? y = some constantJ) (constantFound : ctx.insts[constantJ]? = some constantInfo)
    (data : constantInfo.data = .data 152 35 [.data 151 57 [],.int literal])
    (guard : signedCC cc = true ∨ Imm12.ofNat? (u64 literal) = none)
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules) :
    next.base.nextVreg = st.base.nextVreg + 2 := by
  obtain ⟨_,_,_,_,_,calls⟩ := stock_cmp_selected_calls inv source clif selected
  obtain ⟨emitFuel,conditionFuel,outputFuel,condition,middle,emitTrace,value,produced,conditionTrace,
    enoughEmit,enoughCondition,enoughOutput,emitter,conditionCall,outputCall⟩ := calls
  obtain ⟨rhsTrace,rhs,_⟩ := stock_cmp_narrow_constant_emitter_selected data_program ctx inv cc half
    enoughEmit typeX typeY notConstantX defined constantFound data guard emitter
  obtain ⟨n,equal⟩ : ∃ n,emitFuel=n+160 := ⟨emitFuel-160,by omega⟩
  rw [equal] at rhs
  obtain ⟨_,_,rx,ry,mapX,mapY,producer,finish⟩ := stock_cmp_narrow_rhs_observed data_program ctx
    (signedCC cc) half cc typeX rhs
  obtain ⟨ny,rfl⟩ := inv.valueReg y ry mapY
  let e := if signedCC cc then (if half then ExtendOp.sxth else .sxtb) else (if half then ExtendOp.uxth else .uxtb)
  have decoded : MInst.ofV (.data 58 8 [.data 59 10 [],.data 93 0 [],.reg .xzr,
      .reg (st.base.fresh .int).1,.reg (.vreg ny .int),
      .data 84 (if signedCC cc then (if half then 5 else 4) else (if half then 1 else 0)) []]) =
      some (.aluRRRExtend .subS .size32 .xzr (st.base.fresh .int).1 (.vreg ny .int) e) := by
    dsimp only [e]
    cases signedCC cc <;> cases half <;> rfl
  have shape : CondShape condition (fun _ => True) := by
    rw [producer]
    refine Or.inr (Or.inr ⟨_,_,condOf cc,rfl,decoded,(condOf_ne_al cc).1,(condOf_ne_al cc).2,?_,fun _ _ => trivial⟩)
    rfl
  obtain ⟨m,c,_,result,producedState⟩ := stock_cmp_condition_observed data_program ctx rfl enoughCondition shape conditionCall
  rw [result] at outputCall
  obtain ⟨_,outputState⟩ := stock_cmp_output_observed data_program ctx enoughOutput outputCall
  rw [outputState,producedState,finish]
  simp only [LState.fresh,LState.emit]
end Backend.Stock.Proof.ScalarCmp
