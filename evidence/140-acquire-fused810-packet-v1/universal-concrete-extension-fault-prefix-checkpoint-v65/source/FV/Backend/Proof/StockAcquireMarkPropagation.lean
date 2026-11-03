import FV.Backend.Proof.StockAcquirePendingConsumerTransfer

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Every actual retained record exposes the complete remaining backward scan. -/
theorem ScansSpec.record_suffix {exec : Nat → State → Except String Scan}
    {indices : List Nat} {before : State} {output : BlockScan}
    (spec : ScansSpec exec indices before output) {record : ScanRecord} (member : record ∈ output.records) :
    ∃ (earlier : List ScanRecord) (suffixIndices : List Nat) (tail : BlockScan),
      output.records = earlier++record::tail.records ∧ ScansSpec exec suffixIndices record.output.state tail := by
  induction spec with
  | nil input => cases member
  | @cons inst indices before scan tail head rest ih =>
    rcases List.mem_cons.mp member with equal | later
    · subst record
      exact ⟨[],indices,tail,rfl,rest⟩
    · obtain ⟨earlier,suffixIndices,suffix,parts,run⟩ := ih later
      refine ⟨⟨inst,before,scan⟩::earlier,suffixIndices,suffix,?_,run⟩
      rw [parts]
      rfl

/-- Actual mark persistence transports an entry mark to every later retained input. -/
theorem ScansSpec.marked_record_input {exec : Nat → State → Except String Scan}
    {indices : List Nat} {before : State} {output : BlockScan}
    (spec : ScansSpec exec indices before output)
    (monotone : ∀ record ∈ output.records,∀ (target : Nat),record.input.sunk[target]! = true → record.output.state.sunk[target]! = true)
    {target : Nat} (marked : before.sunk[target]! = true) :
    ∀ record ∈ output.records,record.input.sunk[target]! = true := by
  induction spec with
  | nil input => intro record member;cases member
  | @cons inst indices before scan tail head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with same | later
    · subst record
      exact marked
    · apply ih (fun actual present => monotone actual (List.mem_cons_of_mem _ present)) ?_ record later
      exact monotone _ (List.mem_cons_self ..) target marked

/-- Actual Stock records have strict backward source order. -/
theorem stock_lower_event_records_reverse_order {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    event.output.records.Pairwise (fun first second => second.inst < first.inst) := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,nodeBi,data,core,build,ordered,
    initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  have actual := runScans_spec (stock_lower_event_scan_run run events)
  have sourceOrder : event.indices.Pairwise (fun first second => second < first) := by
    obtain ⟨_,_,_,_,indicesEq,_⟩ := stock_lowerBlockCore_scanOrigin coreRun
    rw [eventEq,indicesEq]
    exact scan_indices_reverse_order _ _
  rw [← actual.order,List.pairwise_map] at sourceOrder
  exact sourceOrder

/-- Marks from a later original consumer reach the actual earlier source record internally. -/
theorem stock_lower_record_mark_propagates {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {first second : ScanRecord}
    (events : event ∈ result.blockScans.toList) (firstMember : first ∈ event.output.records)
    (secondMember : second ∈ event.output.records) (order : second.inst < first.inst)
    {target : Nat} (marked : first.output.state.sunk[target]! = true) : second.input.sunk[target]! = true := by
  have actual := runScans_spec (stock_lower_event_scan_run run events)
  obtain ⟨earlier,suffixIndices,tail,parts,suffixRun⟩ := ScansSpec.record_suffix actual firstMember
  have reverseOrder := stock_lower_event_records_reverse_order run events
  rw [parts] at secondMember reverseOrder
  have inTail : second ∈ tail.records := by
    rcases List.mem_append.mp secondMember with earlierMember | later
    · have backwards := (List.pairwise_append.mp reverseOrder).2.2 second earlierMember first (List.mem_cons_self ..)
      omega
    · rcases List.mem_cons.mp later with same | member
      · subst second
        omega
      · exact member
  apply ScansSpec.marked_record_input suffixRun ?_ marked second inTail
  intro record member producer present
  have retained : record ∈ event.output.records := by
    rw [parts]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ member)
  obtain ⟨pending,marks,monotone,sources⟩ := stock_lower_record_all_source_sunk_updates run events retained
  exact monotone producer present

end Backend.Stock.Proof.Acquire810
