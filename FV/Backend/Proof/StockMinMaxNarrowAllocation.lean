import FV.Backend.Proof.StockMinMaxNarrowShape
import FV.Backend.Proof.StockMinMaxWideCalls
import FV.Backend.Proof.StockSelectDecodedObserved
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open MinMaxRegisterFixture Backend.Stock.Proof.ScalarCmp
/-- Actual narrow minmax selection advances two registers independently of values,
source classifications or final-alias separation. -/
theorem stock_minmax_narrow_selected_allocation {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (unsigned maximum half : Bool) {ty : Clif.Ty}
    (sourceTy : ty = if half then .i16 else .i8) {i x y : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (minmaxOperation unsigned maximum) ty x y))
    (typeX : ctx.valueType? x = some (.int (if half then 16 else 8)))
    (typeY : ctx.valueType? y = some (.int (if half then 16 else 8)))
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules) :
    next.base.nextVreg = st.base.nextVreg+2 := by
  obtain ⟨_,_,_,_,emitFuel,selectFuel,condition,middle,emitTrace,value,produced,selectTrace,
    enoughEmit,enoughSelect,emitter,consumer,output⟩ := stock_minmax_wide_selected_calls inv unsigned maximum source clif selected
  obtain ⟨mi,conditionEq,frontier,_⟩ := stock_minmax_narrow_emitter_shape inv unsigned maximum half typeX typeY enoughEmit emitter
  rw [conditionEq] at consumer
  have width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64 := by
    rw [sourceTy]; cases half <;> simp [Clif.Ty.width]
  obtain ⟨m,_,_,_,rx,ry,_,_,valueEq,finish⟩ := stock_select_flags_decoded_observed data_program ctx rfl enoughSelect width
    (condOf (minmaxComparison unsigned maximum)) consumer
  rw [valueEq,stock_ctor_baseOnly ctx T.output _ produced (by decide)] at output
  change ExtResult.ok (.regsVec [[(middle.base.fresh .int).1]],produced) = .ok (out,next) at output
  have both := Prod.mk.inj (ExtResult.ok.inj output)
  rw [← both.2,finish]
  simp only [LState.fresh,LState.emit]
  rw [frontier]
end Backend.Stock.Proof.ScalarSelect
