import FV.Backend.Proof.StockAcquireActualScanColorOrder

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Nonstrict metadata order reflects original source-slot order, including equal colors. -/
theorem source_color_le_reflects_slots {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : LState} (built : Backend.buildCtx f = .ok (ctx,ranges,initial)) {first second : Nat}
    (firstMember : some first ∈ sourceColorEvents ctx ranges) (secondMember : some second ∈ sourceColorEvents ctx ranges)
    (before : (sourceMetadata ctx ranges).entryColor[first]! ≤ (sourceMetadata ctx ranges).entryColor[second]!) :
    first ≤ second := by
  by_cases strict : (sourceMetadata ctx ranges).entryColor[first]! < (sourceMetadata ctx ranges).entryColor[second]!
  · exact Nat.le_of_lt (source_color_order_reflects_slots built first second firstMember secondMember strict)
  · have equal : (sourceMetadata ctx ranges).entryColor[first]! = (sourceMetadata ctx ranges).entryColor[second]! := by omega
    have firstLookup := source_color_event_lookup built first firstMember
    have secondLookup := source_color_event_lookup built second secondMember
    rw [equal] at firstLookup
    exact Nat.le_of_eq (Option.some.inj (Option.some.inj (firstLookup.symm.trans secondLookup)))

/-- Selected acquires occur in nondecreasing original producer order in the actual forward scan assembly. -/
theorem stock_lower_acquire_forward_producer_order {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {first second : ScanRecord} {pre middle post : List ScanRecord}
    (parts : event.output.records.reverse = pre++first::(middle++second::post))
    {firstStep secondStep : Step}
    (firstRecorded : first.output.step = some firstStep) (firstEmitted : firstStep.decision = .emitted)
    (firstSelected : firstStep.rules.getLast? = some 810)
    (secondRecorded : second.output.step = some secondStep) (secondEmitted : secondStep.decision = .emitted)
    (secondSelected : secondStep.rules.getLast? = some 810) :
    ∃ (R1 : SourceEndpointReceipt f event first) (R2 : SourceEndpointReceipt f event second),R1.producer ≤ R2.producer := by
  have firstMem : first ∈ event.output.records := List.mem_reverse.mp (by rw [parts];simp)
  have secondMem : second ∈ event.output.records := List.mem_reverse.mp (by rw [parts];simp)
  obtain ⟨R1⟩ := stock_lower_acquire_source_endpoint_receipt run scope dominated events firstMem firstRecorded firstEmitted firstSelected
  obtain ⟨R2⟩ := stock_lower_acquire_source_endpoint_receipt run scope dominated events secondMem secondRecorded secondEmitted secondSelected
  have source1 : some R1.producer ∈ sourceColorEvents R1.original R1.ranges := by
    rw [R1.position]
    exact original_colored_statement_event R1.built R1.blockAt R1.producerAt (by rw [R1.atomic];rfl)
  have source2 : some R2.producer ∈ sourceColorEvents R2.original R2.ranges := by
    rw [R2.position]
    exact original_colored_statement_event R2.built R2.blockAt R2.producerAt (by rw [R2.atomic];rfl)
  have sourceBuildEq := Except.ok.inj (R2.built.symm.trans R1.built)
  have ctxEq := congrArg Prod.fst sourceBuildEq
  have rangesEq := congrArg (fun value => value.2.1) sourceBuildEq
  dsimp only at ctxEq rangesEq
  rw [ctxEq,rangesEq] at source2
  obtain ⟨actual,ranges,initial,built,func,table⟩ := stock_lower_record_color_events run events firstMem
  rw [← sourceMetadata_color_events] at table
  have buildEq := Except.ok.inj (built.symm.trans R1.built)
  have actualEq := congrArg Prod.fst buildEq
  have actualRanges := congrArg (fun value => value.2.1) buildEq
  dsimp only at actualEq actualRanges
  rw [actualEq,actualRanges] at table
  have firstEntries := ((((stock_lower_zeroColorLe run).2 event events).2 first firstMem).1).1
  have secondEntries := ((((stock_lower_zeroColorLe run).2 event events).2 second secondMem).1).1
  have secondMetadata : second.input.entryColor = (sourceMetadata R1.original R1.ranges).entryColor :=
    secondEntries.trans (firstEntries.symm.trans table)
  obtain ⟨positive1,color1⟩ := stock_lower_acquire_original_definition_color run scope events firstMem firstRecorded firstEmitted firstSelected
    R1.rootInstalled R1.rootSource R1.defined
  obtain ⟨positive2,color2⟩ := stock_lower_acquire_original_definition_color run scope events secondMem secondRecorded secondEmitted secondSelected
    R2.rootInstalled R2.rootSource R2.defined
  have ordered := List.pairwise_reverse.mpr (stock_lower_event_record_colors_order run scope events)
  rw [parts] at ordered
  have related := (List.pairwise_cons.mp (List.pairwise_append.mp ordered).2.1).1 second
    (List.mem_append_right middle (List.mem_cons_self ..))
  have bound := related _ color2 _ color1
  rw [table,secondMetadata] at bound
  exact ⟨R1,R2,source_color_le_reflects_slots R1.built source1 source2 bound⟩

end Backend.Stock.Proof.Acquire810
