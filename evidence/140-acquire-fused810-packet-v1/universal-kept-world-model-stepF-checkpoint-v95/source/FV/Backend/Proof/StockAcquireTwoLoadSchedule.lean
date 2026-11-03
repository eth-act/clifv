import FV.Backend.Proof.StockAcquireTwoLoadEndpoints

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- The fixed traversal observation exposes its five actual records without an external schedule. -/
theorem actual_schedule_records {event : BlockScanEvent} (schedule : ActualSchedule event) :
    ∃ (first second consumer0 consumer1 terminal : ScanRecord),
      event.output.records.reverse = [first,second,consumer0,consumer1,terminal] ∧
      first.inst = 0 ∧ second.inst = 1 ∧ consumer0.inst = 2 ∧ consumer1.inst = 3 ∧ terminal.inst = 4 := by
  have indices := schedule.2.1
  obtain ⟨first,tail0,parts0,pos0,indices0⟩ := List.map_eq_cons_iff.mp indices
  obtain ⟨second,tail1,parts1,pos1,indices1⟩ := List.map_eq_cons_iff.mp indices0
  obtain ⟨consumer0,tail2,parts2,pos2,indices2⟩ := List.map_eq_cons_iff.mp indices1
  obtain ⟨consumer1,tail3,parts3,pos3,indices3⟩ := List.map_eq_cons_iff.mp indices2
  obtain ⟨terminal,tail4,parts4,pos4,indices4⟩ := List.map_eq_cons_iff.mp indices3
  have empty := List.eq_nil_of_map_eq_nil indices4
  exact ⟨first,second,consumer0,consumer1,terminal,by rw [parts0,parts1,parts2,parts3,parts4,empty],pos0,pos1,pos2,pos3,pos4⟩

/-- The actual size observation aligns every recorded event with the ABI-entry event. -/
theorem actual_single_event {result : Result} (size : result.blockScans.size = 1)
    {first second : BlockScanEvent} (left : first ∈ result.blockScans.toList)
    (right : second ∈ result.blockScans.toList) : first = second := by
  have length : result.blockScans.toList.length = 1 := by simpa using size
  obtain ⟨only,parts⟩ := List.length_eq_one_iff.mp length
  rw [parts] at left right
  exact (List.mem_singleton.mp left).trans (List.mem_singleton.mp right).symm

end Backend.Stock.Proof.AcquireTwoLoadPrefix
