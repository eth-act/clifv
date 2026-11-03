import FV.Backend.Proof.StockAcquireCutSourceBound

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Every earlier original effect lies below the inclusive actual record source cut. -/
theorem stock_lower_record_prefix_cut_above {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) {original : Ctx} {ranges : Array (Nat × Nat)} {initial : LState}
    (built : Backend.buildCtx f = .ok (original,ranges,initial)) {earlier suffix : List Nat}
    (parts : event.indices = (earlier++[record.inst])++suffix) {producer : Nat}
    (source : some producer ∈ sourceColorEvents original ranges) (before : producer < record.inst) :
    (sourceMetadata original ranges).entryColor[producer]! <
      (earlier++[record.inst]).foldl (referenceCut (sourceMetadata original ranges).entryColor) 0 := by
  have reverse := stock_lower_event_indices_reverse run scope events
  rw [parts] at reverse
  have prefixReverse := (List.pairwise_append.mp reverse).1
  have crossed : ∀ inst ∈ earlier++[record.inst],producer < inst := by
    intro inst member
    rcases List.mem_append.mp member with earlierMember | lastMember
    · have relation := (List.pairwise_append.mp prefixReverse).2.2 inst earlierMember record.inst (List.mem_cons_self ..)
      omega
    · have equal : inst = record.inst := by simpa using lastMember
      omega
  obtain ⟨other,otherRanges,otherInitial,bi,block,otherBuilt,blockAt,termEq,indicesEq,
    terminalSource,notSunk,entryColors,metadata⟩ := stock_lower_event_cut_source run scope events
  have equal := Except.ok.inj (built.symm.trans otherBuilt)
  simp only [Prod.mk.injEq] at equal
  rcases equal with ⟨rfl,rfl,rfl⟩
  cases earlier with
  | nil =>
    have compared := List.cons.inj (indicesEq.symm.trans parts)
    have first : record.inst = event.termInst := compared.1.symm
    simpa only [List.nil_append,first] using source_reference_fold_above otherBuilt source terminalSource
      (first ▸ before) [] (by simp)
  | cons first earlier =>
    have compared := List.cons.inj (indicesEq.symm.trans parts)
    have firstEq : first = event.termInst := compared.1.symm
    have firstBefore := crossed first (List.mem_append_left _ (List.mem_cons_self ..))
    have tailBefore : ∀ inst ∈ earlier++[record.inst],producer < inst := by
      intro inst member
      exact crossed inst (List.mem_cons_of_mem _ member)
    subst first
    exact source_reference_fold_above otherBuilt source terminalSource firstBefore (earlier++[record.inst]) tailBefore

/-- Actual retained records classify every crossed original effect as a successful source read frame. -/
theorem stock_lower_record_crossed_source_reads {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {final : Nat} (color : record.output.state.color = some final) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState) (queue : List Nat),
      Backend.buildCtx f = .ok (original,ranges,initial) ∧
      (∀ producer ∈ queue,SourceReadFrame event.ctx producer) ∧
      ∀ producer,some producer ∈ sourceColorEvents original ranges → producer < record.inst →
        final ≤ (sourceMetadata original ranges).entryColor[producer]! →
        producer ∈ queue ∧ SourceReadFrame event.ctx producer := by
  obtain ⟨original,ranges,initial,earlier,scan,suffix,groups,built,prefixRun,boundary,parts,indexParts,
    frontiers,exactSunk,covered⟩ := stock_lower_record_output_read_queue_cut run scope events records
  refine ⟨original,ranges,initial,groups.flatten,built,covered.2,?_⟩
  intro producer source before lower
  have upper := stock_lower_record_prefix_cut_above run scope events built indexParts source before
  have member := covered.1 final color producer source lower upper
  exact ⟨member,covered.2 producer member⟩

end Backend.Stock.Proof.Acquire810
