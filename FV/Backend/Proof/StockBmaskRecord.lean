module

public import FV.Backend.Proof.StockBmaskMatch
public import FV.Backend.Proof.StockBmaskSemantics
public import FV.Backend.Proof.StockFreshRecordValues

@[expose] public section

namespace Backend.Stock.Proof.ScalarMask
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem scan_frontier (st : State) (i : Nat) :
    (scanState st i).base.nextVreg = st.base.nextVreg := by
  unfold scanState; dsimp only; split <;> rfl
private theorem scan_empty (st : State) (i : Nat) :
    (scanState st i).base.emitted = #[] := by
  unfold scanState; dsimp only; split <;> rfl

private theorem helper_shape (st : LState) {wi : Nat} (x : Nat)
    (input : wi = 8 ∨ wi = 16 ∨ wi = 32 ∨ wi = 64) :
    bmaskResult st wi (.vreg x .int) = .vreg (bmaskResultNum wi st.nextVreg) .int ∧
    (bmaskBase st wi (.vreg x .int)).nextVreg = st.nextVreg+bmaskAlloc wi ∧
    (bmaskBase st wi (.vreg x .int)).emitted.toList = st.emitted.toList ++ bmaskCode wi st.nextVreg x := by
  rcases input with rfl | rfl | rfl | rfl
  all_goals simp [bmaskResult,bmaskResultNum,bmaskBase,bmaskAlloc,bmaskCode,bmaskMaskedBase,
    bmaskNarrowBase,LState.fresh,LState.emit,szOf,Array.toList_push,List.append_assoc]

/-- A successful whole-driver record derives the selected original operand,
fresh result, actual result binding, exact emitted template and full bound
state internally. Both one- and two-allocation paths retain their input scope. -/
theorem stock_lower_bmask_record {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {ty : Clif.Ty} {x z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.bmask ty x))
    (results : info.results = [z]) (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ wi nx next,
      (wi = 8 ∨ wi = 16 ∨ wi = 32 ∨ wi = 64) ∧ event.ctx.valueType? x = some (.int wi) ∧
      event.ctx.valueReg? x = some (.vreg nx .int) ∧
      DemandAllowed event.ctx (scanState record.input record.inst) x ∧
      step.results = [[.vreg (bmaskResultNum wi record.input.base.nextVreg) .int]] ∧
      next = {(scanState record.input record.inst).mark x with
        base := bmaskBase (scanState record.input record.inst).base wi (.vreg nx .int)} ∧
      record.output.state = {next with alias := aliasStep next.alias (a,bmaskResultNum wi record.input.base.nextVreg)} ∧
      record.output.emitted.toList = bmaskCode wi record.input.base.nextVreg nx ∧
      record.output.state.base.nextVreg = record.input.base.nextVreg+bmaskAlloc wi := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have inv := (stock_lower_record_context run scope events).1
  obtain ⟨wi,width,typed,safe,r,mapX,outEq,nextEq⟩ := stock_bmask_selected inv source clif receipt.selected
  obtain ⟨nx,rfl⟩ := inv.valueReg x r mapX
  have shape := helper_shape (scanState record.input record.inst).base nx width
  rw [shape.1,scan_frontier] at outEq
  have rss : receipt.results = [[.vreg (bmaskResultNum wi record.input.base.nextVreg) .int]] :=
    V.regsVec.inj (receipt.output.symm.trans outEq)
  have installed := bindResults_virtual event.ctx receipt.next
    [(z,a,bmaskResultNum wi record.input.base.nextVreg)] (by
      intro p member; have same := List.mem_singleton.mp member; subst p; exact mapped)
  simp only [List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil] at installed
  have binding := receipt.binding
  have infoBang : event.ctx.insts[record.inst]! = info := by simp only [getElem!_def,source]
  rw [infoBang,results,rss] at binding
  simp only [List.zip_cons_cons,List.zip_nil_left] at binding
  rw [installed] at binding
  have pairEq := Except.ok.inj binding
  have boundEq := congrArg Prod.fst pairEq
  have copiesEq := congrArg Prod.snd pairEq
  dsimp only at boundEq copiesEq
  have stateEq := receipt.state.trans boundEq.symm
  have rawCode : receipt.next.base.emitted.toList = bmaskCode wi record.input.base.nextVreg nx := by
    rw [nextEq,shape.2.2,scan_empty]
    simp only [Array.toList_empty,List.nil_append,scan_frontier]
  have code : record.output.emitted.toList = bmaskCode wi record.input.base.nextVreg nx := by
    rw [receipt.code,← boundEq,← copiesEq]
    simpa only [Array.append_empty] using rawCode
  refine ⟨wi,nx,receipt.next,width,typed,mapX,safe,receipt.resultRegs.trans rss,nextEq,stateEq,code,?_⟩
  rw [stateEq,nextEq]
  simpa only [scan_frontier] using shape.2.1

end Backend.Stock.Proof.ScalarMask
