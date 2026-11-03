import FV.Backend.Proof.StockAcquireRecordColorGap

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Every actual reverse scan propagates its real source-event interval. -/
theorem ScansSpec.source_color_gap_progress {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {original : Ctx} {ranges : Array (Nat × Nat)} {initial : LState}
    (built : Backend.buildCtx f = .ok (original,ranges,initial))
    (metadata : ∀ record ∈ event.output.records,record.input.entryColor = (sourceMetadata original ranges).entryColor)
    {indices : List Nat} {before : State} {output : BlockScan}
    (spec : ScansSpec (fun inst state => scanInstruction event.ctx event.block inst event.termInst event.isBranch state)
      indices before output) :
    ∀ cut,(∀ record ∈ output.records,record ∈ event.output.records) →
      indices.Pairwise (fun first second => second < first) →
      ColorTailBound (sourceMetadata original ranges).entryColor cut indices →
      SourceColorGap original ranges cut before →
      SourceColorGap original ranges
        (indices.foldl (referenceCut (sourceMetadata original ranges).entryColor) cut) output.state := by
  induction spec with
  | nil input => intro cut kept reverse bounded covered; exact covered
  | @cons inst indices before scan tail head rest ih =>
    intro cut kept reverse bounded covered
    let record : ScanRecord := ⟨inst,before,scan⟩
    have member : record ∈ event.output.records := kept record (List.mem_cons_self ..)
    have entryColors := metadata record member
    have bounds := referenceCut_tail_bound (source_metadata_positive_order built) reverse bounded
    have sunkBound : record.input.sunk[record.inst]! = true →
        referenceCut record.input.entryColor cut record.inst ≤ cut := by
      intro marked
      simpa only [entryColors] using bounds.1
    have after := stock_lower_record_source_color_gap run events member built entryColors covered sunkBound
    have afterCut : SourceColorGap original ranges
        (referenceCut (sourceMetadata original ranges).entryColor cut inst) scan.state := by
      simpa only [entryColors] using after
    exact ih (referenceCut (sourceMetadata original ranges).entryColor cut inst)
      (fun retained member => kept retained (List.mem_cons_of_mem _ member))
      (List.pairwise_cons.mp reverse).2 bounds.2 afterCut

private theorem referenceCut_zero (colors : Array Nat) (inst : Nat) : referenceCut colors 0 inst = colors[inst]! := by
  unfold referenceCut
  split
  · rename_i zero; exact zero.symm
  · rfl

/-- The actual unsunk terminator derives the initial source interval internally. -/
theorem ScansSpec.source_color_gap_from_term {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {original : Ctx} {ranges : Array (Nat × Nat)} {initial : LState}
    (built : Backend.buildCtx f = .ok (original,ranges,initial))
    (metadata : ∀ record ∈ event.output.records,record.input.entryColor = (sourceMetadata original ranges).entryColor)
    {terminal : Nat} {indices : List Nat} {output : BlockScan}
    (spec : ScansSpec (fun inst state => scanInstruction event.ctx event.block inst event.termInst event.isBranch state)
      (terminal::indices) event.input output)
    (kept : ∀ record ∈ output.records,record ∈ event.output.records)
    (notSunk : event.input.sunk[terminal]! = false)
    (reverse : indices.Pairwise (fun first second => second < first))
    (bounded : ColorTailBound (sourceMetadata original ranges).entryColor
      (sourceMetadata original ranges).entryColor[terminal]! indices) :
    SourceColorGap original ranges
      ((terminal::indices).foldl (referenceCut (sourceMetadata original ranges).entryColor) 0) output.state := by
  obtain ⟨scan,tail,head,rest,equal⟩ := ScansSpec.cons_inv spec
  let record : ScanRecord := ⟨terminal,event.input,scan⟩
  have member : record ∈ event.output.records := by
    apply kept record
    rw [equal]
    exact List.mem_cons_self ..
  have entryColors := metadata record member
  have sunkBound : record.input.sunk[record.inst]! = true →
      referenceCut record.input.entryColor 0 record.inst ≤ 0 := by
    intro marked
    rw [notSunk] at marked
    cases marked
  have after := stock_lower_record_source_color_gap run events member built entryColors
    (SourceColorGap.zero original ranges event.input) sunkBound
  have afterCut : SourceColorGap original ranges (sourceMetadata original ranges).entryColor[terminal]! scan.state := by
    simpa only [entryColors,referenceCut_zero] using after
  have tailKept : ∀ retained ∈ tail.records,retained ∈ event.output.records := by
    intro retained member
    apply kept retained
    rw [equal]
    exact List.mem_cons_of_mem _ member
  have finished := ScansSpec.source_color_gap_progress run events built metadata rest
    (sourceMetadata original ranges).entryColor[terminal]! tailKept reverse bounded afterCut
  rw [equal]
  simpa only [List.foldl_cons,referenceCut_zero] using finished

/-- Original Stock scope derives complete prefix intervals without a caller boundary certificate. -/
theorem stock_lower_scan_prefix_source_color_gap {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {indices suffix : List Nat} {output : BlockScan}
    (spec : ScansSpec (fun inst state => scanInstruction event.ctx event.block inst event.termInst event.isBranch state)
      indices event.input output)
    (parts : event.indices = indices++suffix)
    (kept : ∀ record ∈ output.records,record ∈ event.output.records) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState),
      Backend.buildCtx f = .ok (original,ranges,initial) ∧
      SourceColorGap original ranges
        (indices.foldl (referenceCut (sourceMetadata original ranges).entryColor) 0) output.state := by
  obtain ⟨original,ranges,initial,bi,block,built,blockAt,termEq,indicesEq,terminalSource,notSunk,entryColors,metadata⟩ :=
    stock_lower_event_cut_source run scope events
  refine ⟨original,ranges,initial,built,?_⟩
  cases indices with
  | nil =>
    rw [ScansSpec.nil_inv spec]
    exact SourceColorGap.zero original ranges event.input
  | cons first indices =>
    have compared := List.cons.inj (indicesEq.symm.trans parts)
    have firstEq : first = event.termInst := compared.1.symm
    subst first
    have bodyParts : ((Array.range block.body.length).map (blockStart f bi+·)).reverse.toList = indices++suffix := compared.2
    have reverse := scan_indices_reverse_order (blockStart f bi) block.body.length
    rw [bodyParts] at reverse
    have tailReverse := (List.pairwise_append.mp reverse).1
    have earlier : ∀ inst ∈ indices,inst < event.termInst := by
      intro inst member
      have bodyMember : inst ∈ ((Array.range block.body.length).map (blockStart f bi+·)).reverse.toList := by
        rw [bodyParts]
        exact List.mem_append_left _ member
      have bounds := scan_indices_bounds (blockStart f bi) block.body.length inst bodyMember
      rw [termEq]
      exact bounds.2
    have bounded := source_event_tail_bound built event.termInst terminalSource earlier
    exact ScansSpec.source_color_gap_from_term run events built metadata spec kept notSunk tailReverse bounded

/-- Every actual record output derives a boundary-free source-color interval. -/
theorem stock_lower_record_output_source_color_gap {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState)
      (earlier : List Nat) (suffix : List ScanRecord),
      Backend.buildCtx f = .ok (original,ranges,initial) ∧
      event.indices = (earlier++[record.inst])++suffix.map (·.inst) ∧
      SourceColorGap original ranges
        ((earlier++[record.inst]).foldl (referenceCut (sourceMetadata original ranges).entryColor) 0)
        record.output.state := by
  have actual := runScans_spec (stock_lower_event_scan_run run events)
  obtain ⟨earlier,scan,suffix,prefixRun,boundary,parts⟩ := ScansSpec.record_output_prefix actual records
  have indexParts : event.indices = (earlier++[record.inst])++suffix.map (·.inst) := by
    have allIndices := ScansSpec.record_indices actual
    rw [parts,List.map_append,ScansSpec.record_indices prefixRun] at allIndices
    exact allIndices.symm
  have kept : ∀ retained ∈ scan.records,retained ∈ event.output.records := by
    intro retained member
    rw [parts]
    exact List.mem_append_left _ member
  obtain ⟨original,ranges,initial,built,gap⟩ := stock_lower_scan_prefix_source_color_gap run scope events prefixRun indexParts kept
  refine ⟨original,ranges,initial,earlier,suffix,built,indexParts,?_⟩
  rw [← boundary]
  exact gap

end Backend.Stock.Proof.Acquire810
