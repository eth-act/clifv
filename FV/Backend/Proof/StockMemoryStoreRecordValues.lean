import FV.Backend.Proof.StockMemoryStoreSelected
import FV.Backend.Proof.StockMemoryStoreEvaluation

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem scan_empty (st : State) (i : Nat) : (scanState st i).base.emitted = #[] := by
  unfold scanState
  dsimp only
  split <;> rfl
private theorem scan_frontier (st : State) (i : Nat) :
    (scanState st i).base.nextVreg = st.base.nextVreg := by
  unfold scanState
  dsimp only
  split <;> rfl
private theorem scan_alias (st : State) (i : Nat) : (scanState st i).alias = st.alias := by
  unfold scanState
  dsimp only
  split <;> rfl

/-- The whole run fixes store code,empty binding,allocation and aliases without external execution certificates. -/
theorem stock_lower_integer_store_record_full (kind : Kind) {ty : Clif.Ty}
    {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {value pointer valueReg pointerReg : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.store kind.sourceOp ty flags value pointer 0))
    (typed : kind.sourceOp = .store → event.ctx.valueType? value = some (.int kind.width.bits))
    (parameter : event.ctx.defInst? pointer = none)
    (pointerMapped : event.ctx.valueReg? pointer = some (.vreg pointerReg .int))
    (valueMapped : event.ctx.valueReg? value = some (.vreg valueReg .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    info.results = [] ∧ DemandAllowed event.ctx (scanState record.input record.inst) value ∧
      step.results = [] ∧
      record.output.state =
        {((scanState record.input record.inst).mark pointer).mark value with
          base := (scanState record.input record.inst).base.emit
            (.store kind.storeOp (.vreg valueReg .int) (.unsignedOffset (.vreg pointerReg .int) 0) flags)} ∧
      record.output.emitted =
        #[.store kind.storeOp (.vreg valueReg .int) (.unsignedOffset (.vreg pointerReg .int) 0) flags] ∧
      record.output.state.base.nextVreg = record.input.base.nextVreg ∧
      record.output.state.alias = record.input.alias ∧
      record.output.state.demand = ((record.input.mark pointer).mark value).demand := by
  obtain ⟨little,out,next,trace,rhsTrace,rootRun,evaluated⟩ := stock_lower_integer_store_selected_receipts kind
    run scope events records source clif typed recorded emitted
  obtain ⟨safe,output,nextEq⟩ := stock_store_rhs_result data_program kind event.ctx (cfg := {}) rfl
    parameter pointerMapped valueMapped flags (scanState record.input record.inst) #[] 999859 evaluated
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have same := Except.ok.inj (receipt.rootRun.symm.trans rootRun)
  have outEq := (Option.some.inj (congrArg Prod.fst same)).trans output
  have nextEq' := (congrArg (fun q => q.2.1) same).trans nextEq
  have resultsEq : receipt.results = [] := V.regsVec.inj (receipt.output.symm.trans outEq)
  have binding := receipt.binding
  rw [resultsEq,List.zip_nil_right] at binding
  change Except.ok (receipt.next,(#[] : Array MInst)) = Except.ok (receipt.bound,receipt.copies) at binding
  have boundEq := (congrArg Prod.fst (Except.ok.inj binding)).symm
  have copiesEq := (congrArg Prod.snd (Except.ok.inj binding)).symm
  dsimp only at nextEq' boundEq copiesEq
  have stateEq := receipt.state.trans (boundEq.trans nextEq')
  have inv := (stock_lower_record_context run scope events).1
  obtain ⟨types,resultTypes,_,length⟩ := inv.resTys _ _ _ source clif
  change some ([] : List Clif.Ty) = some types at resultTypes
  cases resultTypes
  have empty : info.results = [] := by
    cases found : info.results with
    | nil => rfl
    | cons head tail => rw [found] at length; cases length
  refine ⟨empty,safe,receipt.resultRegs.trans resultsEq,stateEq,?_,?_,?_,?_⟩
  · rw [receipt.code,boundEq,copiesEq,nextEq']
    change (scanState record.input record.inst).base.emitted.push
      (.store kind.storeOp (.vreg valueReg .int) (.unsignedOffset (.vreg pointerReg .int) 0) flags) ++ #[] = _
    rw [scan_empty]
    rfl
  · rw [stateEq]
    exact scan_frontier record.input record.inst
  · rw [stateEq]
    exact scan_alias record.input record.inst
  · rw [stateEq]
    change (((scanState record.input record.inst).mark pointer).mark value).demand = _
    simp only [State.mark,scanState_demands]

end Backend.Stock.Memory.StoreRoots
