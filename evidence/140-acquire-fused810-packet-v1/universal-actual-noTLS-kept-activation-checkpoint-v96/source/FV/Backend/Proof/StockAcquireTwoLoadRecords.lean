import FV.Backend.Proof.StockAcquireTwoLoadReturnedFrames
import FV.Backend.Proof.StockAcquireTwoLoadSchedule

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- Internal metadata for the complete actual traversal; public execution wrappers derive it from lowering. -/
structure TwoLoadRecords (event : BlockScanEvent) where
  first : ScanRecord
  second : ScanRecord
  consumer0 : ScanRecord
  consumer1 : ScanRecord
  terminal : ScanRecord
  parts : event.output.records.reverse = [first,second,consumer0,consumer1,terminal]
  pos0 : first.inst = 0
  pos1 : second.inst = 1
  pos2 : consumer0.inst = 2
  pos3 : consumer1.inst = 3
  pos4 : terminal.inst = 4
  firstState : first.output.state = event.output.state
  secondState : second.output.state = first.input
  consumer0State : consumer0.output.state = second.input
  consumer1State : consumer1.output.state = consumer0.input
  terminalState : terminal.output.state = consumer1.input
  marked0 : first.input.sunk[first.inst]! = true
  marked1 : second.input.sunk[second.inst]! = true
  step0 : Step
  step1 : Step
  recorded0 : consumer0.output.step = some step0
  recorded1 : consumer1.output.step = some step1
  selected0 : step0.rules.getLast? = some 810
  selected1 : step1.rules.getLast? = some 810
  emitted0 : step0.decision = .emitted
  emitted1 : step1.decision = .emitted
  R0 : SourceEndpointReceipt function event consumer0
  R1 : SourceEndpointReceipt function event consumer1

/-- Every named record is retained by the actual event. -/
theorem TwoLoadRecords.member {event : BlockScanEvent} (records : TwoLoadRecords event) (record : ScanRecord)
    (member : record ∈ [records.first,records.second,records.consumer0,records.consumer1,records.terminal]) :
    record ∈ event.output.records := by
  apply List.mem_reverse.mp
  rw [records.parts]
  exact member

/-- Successful original lowering derives the full traversal metadata and both matched endpoint receipts internally. -/
theorem actual_two_load_records {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function) (dominated : Dominated function)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) (schedule : ActualSchedule event) : Nonempty (TwoLoadRecords event) := by
  obtain ⟨first,second,consumer0,consumer1,terminal,parts,pos0,pos1,pos2,pos3,pos4⟩ := actual_schedule_records schedule
  have member0 : consumer0 ∈ event.output.records := by apply List.mem_reverse.mp;rw [parts];simp
  have member1 : consumer1 ∈ event.output.records := by apply List.mem_reverse.mp;rw [parts];simp
  rcases schedule with ⟨eventBlock,indices,state0,state1,state2,state3,state4,mark0,mark1,root0,root1,emitted0,emitted1⟩
  have choose : ∀ (record : ScanRecord),record.output.step.map (·.rules.getLast?) = some (some 810) →
      record.output.step.map (·.decision) = some .emitted →
      ∃ step : Step,record.output.step = some step ∧ step.rules.getLast? = some 810 ∧ step.decision = .emitted := by
    intro record root emitted
    cases found : record.output.step with
    | none => simp only [found,Option.map_none] at root;cases root
    | some step => exact ⟨step,rfl,Option.some.inj (by simpa only [found,Option.map_some] using root),
        Option.some.inj (by simpa only [found,Option.map_some] using emitted)⟩
  obtain ⟨step0,recorded0,selected0,decision0⟩ := choose consumer0
    (by simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using root0)
    (by simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using emitted0)
  obtain ⟨step1,recorded1,selected1,decision1⟩ := choose consumer1
    (by simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using root1)
    (by simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using emitted1)
  obtain ⟨R0⟩ := stock_lower_acquire_source_endpoint_receipt run scope dominated events member0 recorded0 decision0 selected0
  obtain ⟨R1⟩ := stock_lower_acquire_source_endpoint_receipt run scope dominated events member1 recorded1 decision1 selected1
  refine ⟨⟨first,second,consumer0,consumer1,terminal,parts,pos0,pos1,pos2,pos3,pos4,
    ?_,?_,?_,?_,?_,?_,?_,step0,step1,recorded0,recorded1,selected0,selected1,decision0,decision1,R0,R1⟩⟩
  · simpa only [parts,List.getElem!_cons_zero] using state0
  · simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using state1
  · simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using state2
  · simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using state3
  · simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using state4
  · simpa only [parts,List.getElem!_cons_zero,pos0] using mark0
  · simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ,pos1] using mark1

end Backend.Stock.Proof.AcquireTwoLoadPrefix
