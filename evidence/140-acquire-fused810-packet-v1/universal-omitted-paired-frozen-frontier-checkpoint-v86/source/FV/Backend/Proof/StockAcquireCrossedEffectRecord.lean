import FV.Backend.Proof.StockAcquireConsumerFrontierStep

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Existing source selection rejects a nonzero effect color when its successor is not the current color. -/
theorem source_rejects_nonadjacent_effect {ctx : Ctx} {state : State} {value producer : Nat}
    (defined : ctx.defInst? value = some producer)
    (positive : state.entryColor[producer]! ≠ 0)
    (separated : state.color ≠ some (state.entryColor[producer]!+1)) :
    Stock.source ctx state value = none := by
  simp [Stock.source,defined,positive,separated]

/-- Every original colored statement crossed by an actual selected acquire is sunk at its real source record.
That record emits no code. This does not classify other instructions inside a later consumer's chunk. -/
theorem stock_lower_acquire_crossed_effect_record_empty {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ R : SourceEndpointReceipt f event record,
      ∀ (crossed : ScanRecord),crossed ∈ event.output.records →
      ∀ (bi j : Nat) (block : Clif.Block) (stm : Clif.Stmt),
        f.blocks[bi]? = some block → block.body[j]? = some stm →
        crossed.inst = blockStart f bi+j → Stock.colored stm.inst = true →
        R.producer ≤ crossed.inst → crossed.inst < record.inst →
        crossed.input.sunk[crossed.inst]! = true ∧ crossed.output.emitted = #[] := by
  obtain ⟨R⟩ := stock_lower_acquire_source_endpoint_receipt run scope dominated events records recorded emitted selectedId
  refine ⟨R,?_⟩
  intro crossed crossedMem bi j block stm blockAt statement current colored lower upper
  obtain ⟨positive,color⟩ := stock_lower_acquire_original_definition_color run scope events records
    recorded emitted selectedId R.rootInstalled R.rootSource R.defined
  obtain ⟨original,ranges,initial,built,metadata,marked⟩ :=
    stock_lower_record_crossed_sources_marked run scope events records color
  have buildEq := Except.ok.inj (R.built.symm.trans built)
  have ctxEq := congrArg Prod.fst buildEq
  have rangesEq := congrArg (fun pair => pair.2.1) buildEq
  dsimp only at ctxEq rangesEq
  have sourceEvent : some crossed.inst ∈ sourceColorEvents original ranges := by
    rw [← ctxEq,← rangesEq,current]
    exact original_colored_statement_event R.built blockAt statement colored
  have producerEvent : some R.producer ∈ sourceColorEvents original ranges := by
    exact source_color_positive_member original ranges R.producer (by rwa [metadata] at positive)
  have colorLe : (sourceMetadata original ranges).entryColor[R.producer]! ≤
      (sourceMetadata original ranges).entryColor[crossed.inst]! := by
    rcases Nat.eq_or_lt_of_le lower with same | strict
    · rw [same]
      exact Nat.le_refl _
    · exact Nat.le_of_lt (source_slot_colors_order built R.producer crossed.inst producerEvent sourceEvent strict)
  have outputMarked := marked crossed.inst sourceEvent upper (by simpa only [metadata] using colorLe)
  have inputMarked := stock_lower_record_mark_propagates run events records crossedMem upper outputMarked
  have actual := ScansSpec.record_run (runScans_spec (stock_lower_event_scan_run run events)) crossed crossedMem
  have outputEq := Except.ok.inj (actual.symm.trans
    (scan_sunk event.ctx event.block crossed.inst event.termInst event.isBranch crossed.input inputMarked))
  exact ⟨inputMarked,congrArg Scan.emitted outputEq⟩

end Backend.Stock.Proof.Acquire810
