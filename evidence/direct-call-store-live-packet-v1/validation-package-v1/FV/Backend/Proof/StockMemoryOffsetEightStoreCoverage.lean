import FV.Backend.Proof.StockMemoryOffsetEightStoreRecord
import FV.Backend.Proof.StockAluOperandCoverage
import FV.Backend.Proof.StockDemandExtent

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Actual demand and original dominance supply both source-available store operands internally. -/
theorem stock_lower_integer_store_eight_operand_coverage (kind : Kind) {ty : Clif.Ty}
    {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) (scope : LowerScope f)
    (dominated : Dominated f) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j)
    {info : IInfo} {value pointer valueReg pointerReg : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.store kind.sourceOp ty flags value pointer 8))
    (typed : kind.sourceOp = .store → event.ctx.valueType? value = some (.int kind.width.bits))
    (parameter : event.ctx.defInst? pointer = none)
    (pointerMapped : event.ctx.valueReg? pointer = some (.vreg pointerReg .int))
    (valueMapped : event.ctx.valueReg? value = some (.vreg valueReg .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∀ key,key = value ∨ key = pointer → Demanded record.output.state key ∧
      key ∈ availOf f (availIn f result.ctx) bi j := by
  obtain ⟨_,_,_,_,_,_,_,demand⟩ := stock_lower_integer_store_eight_record kind run scope events records
    source clif typed parameter pointerMapped valueMapped recorded emitted
  have valueBound := (Extent.lower_mapped_demand_bounds run scope events records valueMapped).1
  have pointerBound := (Extent.lower_mapped_demand_bounds run scope events records pointerMapped).1
  have wantedValue : Demanded ((record.input.mark pointer).mark value) value :=
    (demanded_mark_iff (record.input.mark pointer) value value
      (by simpa only [State.mark,Array.size_modify] using valueBound)).mpr (Or.inl rfl)
  have wantedPointer : Demanded ((record.input.mark pointer).mark value) pointer := by
    apply (demanded_mark_iff (record.input.mark pointer) value pointer
      (by simpa only [State.mark,Array.size_modify] using valueBound)).mpr
    exact Or.inr ((demanded_mark_iff record.input pointer pointer pointerBound).mpr (Or.inl rfl))
  have available := stock_lower_record_args_available run scope dominated events block statement current source clif
  intro key member
  rcases member with rfl | rfl
  · refine ⟨?_,available key (by simp [Driver.instArgs])⟩
    change record.output.state.demand[key]! ≠ 0
    rw [demand]
    exact wantedValue
  · refine ⟨?_,available key (by simp [Driver.instArgs])⟩
    change record.output.state.demand[key]! ≠ 0
    rw [demand]
    exact wantedPointer

end Backend.Stock.Memory.StoreRoots
