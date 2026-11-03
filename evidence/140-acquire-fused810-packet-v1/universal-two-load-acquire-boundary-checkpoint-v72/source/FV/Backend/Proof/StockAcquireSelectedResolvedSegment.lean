import FV.Backend.Proof.StockAcquireMachineBoundaryAllWidthsW
import FV.Backend.Proof.StockBlockCode

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The actual whole-driver code contains the selected acquire with its final pointer alias and fresh result. -/
theorem stock_lower_acquire_selected_resolved_segment {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (R : SourceEndpointReceipt f event record) (pointerReg dest resultId key label index : Nat) (block : VBlock),
      event.ctx.valueReg? R.pointer = some (.vreg pointerReg .int) ∧
      R.rootInfo.results = [resultId] ∧ event.ctx.valueReg? resultId = some (.vreg key .int) ∧
      dest = record.input.base.nextVreg ∧ aliasNum result.final.alias dest = dest ∧
      (result.final.alias[key]?).join = some dest ∧ aliasNum result.final.alias key = dest ∧
      result.code.blocks[label]? = some block ∧
      SegAt block index [.loadAcquire (CTy.ofClif R.ty) (.vreg dest .int)
        (.vreg (aliasNum result.final.alias pointerReg) .int) R.flags] := by
  obtain ⟨R,pointerReg,dest,resultId,key,register,results,resultReg,fresh,chunk,resultRegisters,finalAlias,finalNum⟩ :=
    stock_lower_acquire_selected_chunk run scope dominated events records recorded emitted selectedId
  have member : record ∈ retainedRecords result.blockScans := List.mem_flatMap.mpr ⟨event,events,records⟩
  have lower := ((stock_lower_record_intervals run).bounds record member).1
  have terminal := (stock_lower_freshAlias_terminal run (n := dest) (by rwa [fresh])).2
  obtain ⟨label,block,index,found,segment⟩ := stock_lower_record_segment run events records
  rw [chunk] at segment
  change SegAt block index [MInst.loadAcquire (CTy.ofClif R.ty)
    (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg dest .int))
    (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg pointerReg .int)) R.flags] at segment
  rw [resolve_vreg,resolve_vreg] at segment
  change SegAt block index [.loadAcquire (CTy.ofClif R.ty) (.vreg (aliasNum result.final.alias dest) .int)
    (.vreg (aliasNum result.final.alias pointerReg) .int) R.flags] at segment
  rw [terminal] at segment
  exact ⟨R,pointerReg,dest,resultId,key,label,index,block,register,results,resultReg,fresh,terminal,finalAlias,finalNum,found,segment⟩

end Backend.Stock.Proof.Acquire810
