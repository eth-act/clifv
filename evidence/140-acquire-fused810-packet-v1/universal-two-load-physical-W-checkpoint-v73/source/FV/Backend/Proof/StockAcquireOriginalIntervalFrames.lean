import FV.Backend.Proof.StockAcquireSelectedSourceEndpoints

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- An actual original operand definition fixes the selected output color uniquely. -/
theorem stock_lower_acquire_original_definition_color {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) {rootInfo : IInfo} {target : Clif.Ty} {value producer : Nat}
    (rootInstalled : event.ctx.insts[record.inst]? = some rootInfo)
    (rootSource : rootInfo.clif = some (.extend .uextend target value))
    (defined : event.ctx.defInst? value = some producer) :
    record.input.entryColor[producer]! ≠ 0 ∧ record.output.state.color = some record.input.entryColor[producer]! := by
  obtain ⟨actualRoot,actualTarget,actualValue,actualProducer,info,ty,flags,pointer,actualInstalled,actualSource,
    actualDefined,installed,source,integer,little,positive,color⟩ :=
    stock_lower_acquire_selected_original_pair run scope events records recorded emitted selectedId
  have infoEq := Option.some.inj (actualInstalled.symm.trans rootInstalled)
  have instEq := Option.some.inj (((congrArg IInfo.clif infoEq).symm.trans actualSource).symm.trans rootSource)
  have valueEq : actualValue = value := (Clif.Inst.extend.inj instEq).2.2
  rw [valueEq] at actualDefined
  have producerEq := Option.some.inj (actualDefined.symm.trans defined)
  rw [producerEq] at positive color
  exact ⟨positive,color⟩

/-- Derived output color and original metadata supply every successful source frame in the complete interval. -/
theorem stock_lower_record_original_interval_frames {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {original : Ctx} {ranges : Array (Nat × Nat)} {initial : LState}
    (built : Backend.buildCtx f = .ok (original,ranges,initial)) {producer : Nat}
    (positive : record.input.entryColor[producer]! ≠ 0)
    (color : record.output.state.color = some record.input.entryColor[producer]!) :
    ∀ (bi j : Nat) (block : Clif.Block) (stm : Clif.Stmt),f.blocks[bi]? = some block →
      block.body[j]? = some stm → producer ≤ blockStart f bi+j → blockStart f bi+j < record.inst →
      SourceReadFrame event.ctx (blockStart f bi+j) := by
  obtain ⟨metaCtx,metaRanges,metaInitial,metaBuilt,func,table⟩ := stock_lower_record_color_events run events records
  have metaEqual := Except.ok.inj (built.symm.trans metaBuilt)
  have metaCtxEq : original = metaCtx := congrArg Prod.fst metaEqual
  have metaRangesEq : ranges = metaRanges := congrArg (fun pair => pair.2.1) metaEqual
  have metadata : record.input.entryColor = (sourceMetadata original ranges).entryColor := by
    rw [← metaCtxEq,← metaRangesEq] at table
    exact table.trans (sourceMetadata_color_events original ranges).symm
  rw [metadata] at positive color
  have producerSource := source_color_positive_member original ranges producer positive
  obtain ⟨queueCtx,queueRanges,queueInitial,earlier,scan,suffix,groups,queueBuilt,prefixRun,boundary,parts,indexParts,
    frontiers,exactSunk,covered⟩ := stock_lower_record_output_read_queue_cut run scope events records
  have queueEqual := Except.ok.inj (built.symm.trans queueBuilt)
  have queueCtxEq : original = queueCtx := congrArg Prod.fst queueEqual
  have queueRangesEq : ranges = queueRanges := congrArg (fun pair => pair.2.1) queueEqual
  rw [← queueCtxEq,← queueRangesEq] at covered
  have view := stock_lower_event_build_source_slots run scope events built
  intro bi j block stm blockAt statement lower upper
  cases effect : Stock.colored stm.inst with
  | false =>
    obtain ⟨actualInfo,present,actualSource,results⟩ := (ctxSpec_of built).facts.stmt bi block j stm blockAt statement
    exact uncolored_source_read_frame (view _ actualInfo stm.inst present actualSource) actualSource effect
  | true =>
    have source := original_colored_statement_event built blockAt statement effect
    have lowerColor : (sourceMetadata original ranges).entryColor[producer]! ≤
        (sourceMetadata original ranges).entryColor[blockStart f bi+j]! := by
      rcases Nat.eq_or_lt_of_le lower with same | less
      · simp only [same,Nat.le_refl]
      · exact Nat.le_of_lt (source_slot_colors_order built _ _ producerSource source less)
    have upperColor := stock_lower_record_prefix_cut_above run scope events built indexParts source upper
    exact covered.source_read color _ source lowerColor upperColor

end Backend.Stock.Proof.Acquire810
