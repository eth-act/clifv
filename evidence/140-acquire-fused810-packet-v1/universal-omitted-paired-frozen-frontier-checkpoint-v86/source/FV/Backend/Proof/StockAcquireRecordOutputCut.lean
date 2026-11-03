import FV.Backend.Proof.StockAcquireActualReadQueueCut

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual scan records retain precisely their scanned instruction indices. -/
theorem ScansSpec.record_indices {exec : Nat → State → Except String Scan}
    {indices : List Nat} {before : State} {output : BlockScan}
    (spec : ScansSpec exec indices before output) : output.records.map (·.inst) = indices := by
  induction spec with
  | nil input => rfl
  | cons head rest ih => simpa only [List.map_cons,ih]

/-- Every actual record supplies its complete inclusive scan prefix. -/
theorem ScansSpec.record_output_prefix {exec : Nat → State → Except String Scan}
    {indices : List Nat} {before : State} {output : BlockScan}
    (spec : ScansSpec exec indices before output) {record : ScanRecord} (member : record ∈ output.records) :
    ∃ (earlier : List Nat) (scan : BlockScan) (suffix : List ScanRecord),
      ScansSpec exec (earlier++[record.inst]) before scan ∧ scan.state = record.output.state ∧
      output.records = scan.records++suffix := by
  induction spec with
  | nil input => cases member
  | @cons inst indices before scan tail head rest ih =>
    rcases List.mem_cons.mp member with equal | member
    · subst record
      refine ⟨[],⟨scan.state,[⟨inst,before,scan⟩],#[]++scan.emitted⟩,tail.records,
        .cons head (.nil scan.state),rfl,rfl⟩
    · obtain ⟨earlier,part,suffix,actual,boundary,parts⟩ := ih member
      refine ⟨inst::earlier,⟨part.state,⟨inst,before,scan⟩::part.records,part.code++scan.emitted⟩,
        suffix,.cons head actual,boundary,?_⟩
      simp only [List.cons_append]
      exact congrArg (fun records => ⟨inst,before,scan⟩::records) parts

/-- The actual retained record derives its output read queue without an external cut certificate. -/
theorem stock_lower_record_output_read_queue_cut {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState)
      (earlier : List Nat) (scan : BlockScan) (suffix : List ScanRecord) (groups : List (List Nat)),
      Backend.buildCtx f = .ok (original,ranges,initial) ∧
      ScansSpec (fun inst state => scanInstruction event.ctx event.block inst event.termInst event.isBranch state)
        (earlier++[record.inst]) event.input scan ∧ scan.state = record.output.state ∧
      event.output.records = scan.records++suffix ∧
      event.indices = (earlier++[record.inst])++suffix.map (·.inst) ∧
      RecordFrontiers f event.ctx scan.records groups ∧
      record.output.state.sunk = groups.flatten.foldl (fun bits producer => bits.set! producer true) event.input.sunk ∧
      ReadQueueCut event.ctx original ranges
        ((earlier++[record.inst]).foldl (referenceCut (sourceMetadata original ranges).entryColor) 0)
        record.output.state groups.flatten := by
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
  obtain ⟨original,ranges,initial,groups,built,entryColors,metadata,frontiers,exactSunk,covered⟩ :=
    stock_lower_scan_prefix_read_queue_cut run scope events prefixRun indexParts kept
  refine ⟨original,ranges,initial,earlier,scan,suffix,groups,built,prefixRun,boundary,parts,indexParts,
    frontiers,?_,?_⟩
  · rw [← boundary]
    exact exactSunk
  · rw [← boundary]
    exact covered

end Backend.Stock.Proof.Acquire810
