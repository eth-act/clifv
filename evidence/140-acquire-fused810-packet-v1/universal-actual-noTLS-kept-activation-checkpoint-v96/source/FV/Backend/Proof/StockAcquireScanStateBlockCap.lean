import FV.Backend.Proof.StockAcquireSelectedSourceCapture

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Every real scan reset is capped by its original terminator, including the first record.
The proof retains inherited entry marks; it does not require them to be empty. -/
theorem stock_lower_record_scan_state_color_cap {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState),
      Backend.buildCtx f = .ok (original,ranges,initial) ∧
      record.input.entryColor = (sourceMetadata original ranges).entryColor ∧
      ColorUpperBound (sourceMetadata original ranges).entryColor[event.termInst]! (scanState record.input record.inst) := by
  obtain ⟨original,ranges,initial,bi,block,built,blockAt,termEq,indicesEq,terminalSource,notSunk,entryColors,metadata⟩ :=
    stock_lower_event_cut_source run scope events
  have recordMeta := metadata record records
  have actual := runScans_spec (stock_lower_event_scan_run run events)
  have indexMember : record.inst ∈ event.indices := by
    rw [← actual.order]
    exact List.mem_map.mpr ⟨record,records,rfl⟩
  have instBound : record.inst ≤ event.termInst := by
    rw [indicesEq] at indexMember
    rcases List.mem_cons.mp indexMember with same | tail
    · omega
    · have bounds := scan_indices_bounds _ _ _ tail
      rw [termEq]
      omega
  have entryBound : record.input.entryColor[record.inst]! ≤ (sourceMetadata original ranges).entryColor[event.termInst]! := by
    rw [recordMeta]
    by_cases zero : (sourceMetadata original ranges).entryColor[record.inst]! = 0
    · rw [zero]
      exact Nat.zero_le _
    · have source := source_color_positive_member original ranges record.inst zero
      by_cases same : record.inst = event.termInst
      · rw [same]
        exact Nat.le_refl _
      · apply Nat.le_of_not_gt
        intro greater
        have wrong := source_color_le_reflects_slots built terminalSource source (Nat.le_of_lt greater)
        omega
  obtain ⟨prefixIndices,prefixScan,suffix,prefixRun,boundary,recordParts⟩ := ScansSpec.record_prefix actual records
  have parts : event.indices = prefixIndices++record.inst::(suffix.map (·.inst)) := by
    rw [← actual.order,recordParts,List.map_append,List.map_cons,prefixRun.order]
  refine ⟨original,ranges,initial,built,recordMeta,?_⟩
  by_cases empty : prefixIndices = []
  · rw [empty,List.nil_append] at parts
    have currentEq := (List.cons.inj (indicesEq.symm.trans parts)).1.symm
    have positive : record.input.entryColor[record.inst]! ≠ 0 := by
      rw [recordMeta,currentEq]
      exact source_color_event_nonzero built event.termInst terminalSource
    apply ColorUpperBound.at_color (scanState_color_positive record.input record.inst positive)
    exact entryBound
  · have kept : ∀ retained ∈ prefixScan.records,retained ∈ event.output.records := by
      intro retained member
      rw [recordParts]
      exact List.mem_append_left _ member
    obtain ⟨other,otherRanges,otherInitial,otherBuilt,capped⟩ :=
      stock_lower_nonempty_prefix_color_upper run scope events prefixRun parts empty kept
    have equal := Except.ok.inj (otherBuilt.symm.trans built)
    have ctxEq := congrArg Prod.fst equal
    have rangesEq := congrArg (fun pair => pair.2.1) equal
    dsimp only at ctxEq rangesEq
    rw [ctxEq,rangesEq,boundary] at capped
    exact scanState_color_upper_bound record.input record.inst capped entryBound

end Backend.Stock.Proof.Acquire810
