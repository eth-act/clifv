import FV.Backend.Proof.StockAcquireColorUpperBound

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual scan decisions propagate a constant original block cap through every sunk alternative. -/
theorem ScansSpec.color_upper_progress {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {indices : List Nat} {before : State} {output : BlockScan}
    (spec : ScansSpec (fun inst state => scanInstruction event.ctx event.block inst event.termInst event.isBranch state)
      indices before output) {cap : Nat} :
    (∀ record ∈ output.records,record ∈ event.output.records) →
    (∀ record ∈ output.records,record.input.entryColor[record.inst]! ≤ cap) →
    ColorUpperBound cap before → ColorUpperBound cap output.state := by
  induction spec with
  | nil input => intro kept entries bounded;exact bounded
  | @cons inst indices before scan tail head rest ih =>
    intro kept entries bounded
    let record : ScanRecord := ⟨inst,before,scan⟩
    have member : record ∈ event.output.records := kept record (List.mem_cons_self ..)
    have entry := entries record (List.mem_cons_self ..)
    have after := stock_lower_record_color_upper_bound run events member (fun _ => bounded)
      (scanState_color_upper_bound before inst bounded entry)
    exact ih (fun retained member => kept retained (List.mem_cons_of_mem _ member))
      (fun retained member => entries retained (List.mem_cons_of_mem _ member)) after

/-- The real unsunk source terminator establishes the cap independently of inherited entry colors. -/
theorem ScansSpec.color_upper_from_term {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {original : Ctx} {ranges : Array (Nat × Nat)} {initial : LState}
    (built : Backend.buildCtx f = .ok (original,ranges,initial))
    (metadata : ∀ record ∈ event.output.records,record.input.entryColor = (sourceMetadata original ranges).entryColor)
    {terminal : Nat} {indices : List Nat} {output : BlockScan}
    (spec : ScansSpec (fun inst state => scanInstruction event.ctx event.block inst event.termInst event.isBranch state)
      (terminal::indices) event.input output)
    (kept : ∀ record ∈ output.records,record ∈ event.output.records)
    (source : some terminal ∈ sourceColorEvents original ranges)
    (notSunk : event.input.sunk[terminal]! = false)
    (bounded : ColorTailBound (sourceMetadata original ranges).entryColor
      (sourceMetadata original ranges).entryColor[terminal]! indices) :
    ColorUpperBound (sourceMetadata original ranges).entryColor[terminal]! output.state := by
  obtain ⟨scan,tail,head,rest,equal⟩ := ScansSpec.cons_inv spec
  let record : ScanRecord := ⟨terminal,event.input,scan⟩
  have member : record ∈ event.output.records := by
    apply kept record
    rw [equal]
    exact List.mem_cons_self ..
  have entryColors := metadata record member
  have positive : event.input.entryColor[terminal]! ≠ 0 := by
    rw [entryColors]
    exact source_color_event_nonzero built terminal source
  have scanBound : ColorUpperBound (sourceMetadata original ranges).entryColor[terminal]!
      (scanState event.input terminal) := by
    apply ColorUpperBound.at_color (scanState_color_positive event.input terminal positive)
    rw [entryColors]
  have after := stock_lower_record_color_upper_bound run events member (fun marked => by
    rw [notSunk] at marked;cases marked) scanBound
  have tailKept : ∀ retained ∈ tail.records,retained ∈ event.output.records := by
    intro retained member
    apply kept retained
    rw [equal]
    exact List.mem_cons_of_mem _ member
  have tailEntries : ∀ retained ∈ tail.records,
      retained.input.entryColor[retained.inst]! ≤ (sourceMetadata original ranges).entryColor[terminal]! := by
    intro retained member
    rw [metadata retained (tailKept retained member)]
    by_cases zero : (sourceMetadata original ranges).entryColor[retained.inst]! = 0
    · rw [zero];omega
    · apply bounded retained.inst
      · rw [← ScansSpec.record_indices rest]
        exact List.mem_map.mpr ⟨retained,member,rfl⟩
      · exact zero
  have finished := ScansSpec.color_upper_progress run events rest tailKept tailEntries after
  rw [equal]
  exact finished

/-- Original ranges and the real terminator derive the bound for every nonempty actual scan prefix. -/
theorem stock_lower_nonempty_prefix_color_upper {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {indices suffix : List Nat} {output : BlockScan}
    (spec : ScansSpec (fun inst state => scanInstruction event.ctx event.block inst event.termInst event.isBranch state)
      indices event.input output)
    (parts : event.indices = indices++suffix) (nonempty : indices ≠ [])
    (kept : ∀ record ∈ output.records,record ∈ event.output.records) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState),
      Backend.buildCtx f = .ok (original,ranges,initial) ∧
      ColorUpperBound (sourceMetadata original ranges).entryColor[event.termInst]! output.state := by
  obtain ⟨original,ranges,initial,bi,block,built,blockAt,termEq,indicesEq,terminalSource,notSunk,entryColors,metadata⟩ :=
    stock_lower_event_cut_source run scope events
  refine ⟨original,ranges,initial,built,?_⟩
  cases indices with
  | nil => exact False.elim (nonempty rfl)
  | cons first indices =>
    have compared := List.cons.inj (indicesEq.symm.trans parts)
    have firstEq : first = event.termInst := compared.1.symm
    subst first
    have bodyParts : ((Array.range block.body.length).map (blockStart f bi+·)).reverse.toList = indices++suffix := compared.2
    have earlier : ∀ inst ∈ indices,inst < event.termInst := by
      intro inst member
      have bodyMember : inst ∈ ((Array.range block.body.length).map (blockStart f bi+·)).reverse.toList := by
        rw [bodyParts]
        exact List.mem_append_left _ member
      have bounds := scan_indices_bounds (blockStart f bi) block.body.length inst bodyMember
      rw [termEq]
      exact bounds.2
    exact ScansSpec.color_upper_from_term run events built metadata spec kept terminalSource notSunk
      (source_event_tail_bound built event.termInst terminalSource earlier)

/-- Every retained record derives its original block's constant terminator-color cap. -/
theorem stock_lower_record_output_color_upper {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState),
      Backend.buildCtx f = .ok (original,ranges,initial) ∧
      ColorUpperBound (sourceMetadata original ranges).entryColor[event.termInst]! record.output.state := by
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
  obtain ⟨original,ranges,initial,built,bounded⟩ := stock_lower_nonempty_prefix_color_upper run scope events
    prefixRun indexParts (by simp) kept
  refine ⟨original,ranges,initial,built,?_⟩
  rw [← boundary]
  exact bounded

end Backend.Stock.Proof.Acquire810
