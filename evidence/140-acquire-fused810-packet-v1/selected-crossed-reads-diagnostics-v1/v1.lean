import FV.Backend.Proof.StockAcquireSourceMemoryComposition

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual acquire selection and binding identify the original source color internally. -/
theorem stock_lower_acquire_output_source_color {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState) value producer info ty flags pointer,
      Backend.buildCtx f = .ok (original,ranges,initial) ∧
      event.ctx.defInst? value = some producer ∧
      event.ctx.insts[producer]? = some info ∧ info.clif = some (.atomicLoad ty flags pointer) ∧
      eTy ty = true ∧ flags.endianness ≠ some .big ∧
      some producer ∈ sourceColorEvents original ranges ∧
      record.output.state.color = some (sourceMetadata original ranges).entryColor[producer]! := by
  obtain ⟨value,producer,info,ty,flags,pointer,out,next,fired,defined,once,installed,source,
    integer,little,rootRun,pending,sunkEq,colorEq⟩ :=
    stock_lower_acquire_selected_singleton run scope events records recorded emitted selectedId
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have nextEq : next = receipt.next := congrArg (fun triple => triple.2.1)
    (Except.ok.inj (rootRun.symm.trans receipt.rootRun))
  obtain ⟨entries,color,sunk⟩ := bindResults_mark_fields receipt.binding
  obtain ⟨original,ranges,initial,built,func,table⟩ := stock_lower_record_color_events run events records
  have metadata : record.input.entryColor = (sourceMetadata original ranges).entryColor :=
    table.trans (sourceMetadata_color_events original ranges).symm
  have positive := pending.member_positive producer (List.mem_cons_self ..)
  rw [scanState_entry_colors,metadata] at positive
  refine ⟨original,ranges,initial,value,producer,info,ty,flags,pointer,built,defined,installed,source,
    integer,little,source_color_positive_member original ranges producer positive,?_⟩
  rw [receipt.state,color,← nextEq,colorEq,scanState_entry_colors,metadata]

/-- Every original source effect between the selected producer and its consumer derives a read frame. -/
theorem stock_lower_acquire_between_source_read_frames {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState) value producer info ty flags pointer,
      Backend.buildCtx f = .ok (original,ranges,initial) ∧
      event.ctx.defInst? value = some producer ∧
      event.ctx.insts[producer]? = some info ∧ info.clif = some (.atomicLoad ty flags pointer) ∧
      eTy ty = true ∧ flags.endianness ≠ some .big ∧
      ∀ target,some target ∈ sourceColorEvents original ranges → producer ≤ target → target < record.inst →
        SourceReadFrame event.ctx target := by
  obtain ⟨original,ranges,initial,value,producer,info,ty,flags,pointer,built,defined,installed,source,
    integer,little,producerSource,color⟩ :=
    stock_lower_acquire_output_source_color run scope events records recorded emitted selectedId
  obtain ⟨other,otherRanges,otherInitial,queue,otherBuilt,reads,covered⟩ :=
    stock_lower_record_crossed_source_reads run scope events records color
  have equal := Except.ok.inj (built.symm.trans otherBuilt)
  simp only [Prod.mk.injEq] at equal
  rcases equal with ⟨rfl,rfl,rfl⟩
  refine ⟨other,otherRanges,otherInitial,value,producer,info,ty,flags,pointer,otherBuilt,defined,installed,
    source,integer,little,?_⟩
  intro target targetSource lower upper
  have colorOrder : (sourceMetadata other otherRanges).entryColor[producer]! ≤
      (sourceMetadata other otherRanges).entryColor[target]! := by
    rcases Nat.eq_or_lt_of_le lower with equal | less
    · rw [equal]
    · exact Nat.le_of_lt (source_slot_colors_order otherBuilt producer target producerSource targetSource less)
  exact (covered target targetSource upper colorOrder).2

end Backend.Stock.Proof.Acquire810
