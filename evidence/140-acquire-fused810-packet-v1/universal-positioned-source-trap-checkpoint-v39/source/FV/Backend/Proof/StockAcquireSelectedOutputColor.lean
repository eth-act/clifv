import FV.Backend.Proof.StockAcquireCrossedReadSources

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual result binding preserves the internally selected deferred producer color. -/
theorem stock_lower_acquire_output_color {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ value producer info ty flags pointer,
      event.ctx.defInst? value = some producer ∧
      event.ctx.insts[producer]? = some info ∧ info.clif = some (.atomicLoad ty flags pointer) ∧
      eTy ty = true ∧ flags.endianness ≠ some .big ∧
      record.output.state.color = some record.input.entryColor[producer]! := by
  obtain ⟨value,producer,info,ty,flags,pointer,out,next,fired,defined,once,installed,original,
    integer,little,rootRun,pending,sunkEq,colorEq⟩ :=
    stock_lower_acquire_selected_singleton run scope events records recorded emitted selectedId
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have same := Except.ok.inj (rootRun.symm.trans receipt.rootRun)
  have nextEq : next = receipt.next := congrArg (fun triple => triple.2.1) same
  obtain ⟨entries,color,sunk⟩ := bindResults_mark_fields receipt.binding
  refine ⟨value,producer,info,ty,flags,pointer,defined,installed,original,integer,little,?_⟩
  rw [receipt.state,color,← nextEq,colorEq,scanState_entry_colors]

end Backend.Stock.Proof.Acquire810
