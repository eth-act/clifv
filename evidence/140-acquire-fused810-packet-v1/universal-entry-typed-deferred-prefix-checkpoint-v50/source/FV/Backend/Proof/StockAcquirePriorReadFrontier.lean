import FV.Backend.Proof.StockAcquireReadScanFrontiers

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A retained record supplies its complete actual scan prefix and exact input boundary. -/
theorem ScansSpec.record_prefix {exec : Nat → State → Except String Scan}
    {indices : List Nat} {before : State} {output : BlockScan}
    (spec : ScansSpec exec indices before output) {record : ScanRecord} (member : record ∈ output.records) :
    ∃ (prefixIndices : List Nat) (scan : BlockScan) (suffix : List ScanRecord),
      ScansSpec exec prefixIndices before scan ∧ scan.state = record.input ∧
      output.records = scan.records++record::suffix := by
  induction spec with
  | nil input => cases member
  | @cons inst indices before scan tail head rest ih =>
    rcases List.mem_cons.mp member with equal | member
    · subst record
      exact ⟨[],⟨before,[],#[]⟩,tail.records,.nil before,rfl,rfl⟩
    · obtain ⟨prefixIndices,prefixScan,suffix,prefixRun,boundary,records⟩ := ih member
      refine ⟨inst::prefixIndices,⟨prefixScan.state,⟨inst,before,scan⟩::prefixScan.records,
        prefixScan.code++scan.emitted⟩,suffix,.cons head prefixRun,boundary,?_⟩
      simp only [List.cons_append]
      exact congrArg (fun records => ⟨inst,before,scan⟩::records) records

/-- Exact source frames and mark updates compose through any actual scan prefix. -/
theorem ScansSpec.read_frontier_groups {f : Clif.Function} {ctx : Ctx}
    {exec : Nat → State → Except String Scan} {indices : List Nat} {before : State} {output : BlockScan}
    (spec : ScansSpec exec indices before output)
    (localFrontier : ∀ record ∈ output.records,∃ pending,RecordFrontier f ctx record pending ∧
      ∀ producer ∈ pending,SourceReadFrame ctx producer) :
    ∃ groups : List (List Nat),RecordFrontiers f ctx output.records groups ∧
      output.state.sunk = groups.flatten.foldl (fun bits producer => bits.set! producer true) before.sunk ∧
      ∀ producer ∈ groups.flatten,SourceReadFrame ctx producer := by
  revert localFrontier
  induction spec with
  | nil input => intro localFrontier; exact ⟨[],.nil,rfl,by simp⟩
  | @cons inst indices before scan tail head rest ih =>
    intro localFrontier
    obtain ⟨pending,front,headFrames⟩ := localFrontier _ (List.mem_cons_self ..)
    obtain ⟨groups,frontiers,exactSunk,tailFrames⟩ := ih (fun record member =>
      localFrontier record (List.mem_cons_of_mem _ member))
    refine ⟨pending::groups,.cons front frontiers,?_,?_⟩
    · simp only [List.flatten_cons,List.foldl_append]
      rw [← front.1]
      exact exactSunk
    · intro producer member
      rcases List.mem_append.mp member with member | member
      · exact headFrames producer member
      · exact tailFrames producer member

/-- Every actual record derives all earlier read groups and its exact sunk frontier. -/
theorem stock_lower_record_prior_read_frontier {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records) :
    ∃ (prefixIndices : List Nat) (scan : BlockScan) (suffix : List ScanRecord) (groups : List (List Nat)),
      ScansSpec (fun inst state => scanInstruction event.ctx event.block inst event.termInst event.isBranch state)
        prefixIndices event.input scan ∧ scan.state = record.input ∧
      event.output.records = scan.records++record::suffix ∧ RecordFrontiers f event.ctx scan.records groups ∧
      record.input.sunk = groups.flatten.foldl (fun bits producer => bits.set! producer true) event.input.sunk ∧
      ∀ producer ∈ groups.flatten,SourceReadFrame event.ctx producer := by
  have actual := runScans_spec (stock_lower_event_scan_run run events)
  obtain ⟨prefixIndices,scan,suffix,prefixRun,boundary,parts⟩ := ScansSpec.record_prefix actual records
  have localFrontier : ∀ retained ∈ scan.records,∃ pending,RecordFrontier f event.ctx retained pending ∧
      ∀ producer ∈ pending,SourceReadFrame event.ctx producer := by
    intro retained member
    apply stock_lower_record_read_frontier run events
    rw [parts]
    exact List.mem_append_left _ member
  obtain ⟨groups,frontiers,exactSunk,frames⟩ := ScansSpec.read_frontier_groups prefixRun localFrontier
  exact ⟨prefixIndices,scan,suffix,groups,prefixRun,boundary,parts,frontiers,boundary ▸ exactSunk,frames⟩

end Backend.Stock.Proof.Acquire810
