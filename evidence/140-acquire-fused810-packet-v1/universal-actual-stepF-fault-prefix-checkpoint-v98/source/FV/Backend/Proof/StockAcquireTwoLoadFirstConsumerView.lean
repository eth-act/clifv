import FV.Backend.Proof.StockAcquireTwoLoadFirstSourceFault
import FV.Backend.Proof.StockAcquireTwoLoadSchedule

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- Both actual sunk producer records are empty; the first consumer begins in the actual event entry state. -/
theorem actual_first_consumer_view {result : Result} (run : Stock.lower function = .ok result)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) (schedule : ActualSchedule event) :
    ∃ (consumer : ScanRecord) (step : Step) (suffixCode : Array MInst),consumer ∈ event.output.records ∧ consumer.inst = 2 ∧
      consumer.output.step = some step ∧ step.rules.getLast? = some 810 ∧ step.decision = .emitted ∧
      consumer.output.state = event.output.state ∧ event.output.code = consumer.output.emitted++suffixCode := by
  obtain ⟨first,second,consumer0,consumer1,terminal,parts,pos0,pos1,pos2,pos3,pos4⟩ := actual_schedule_records schedule
  have member0 : first ∈ event.output.records := by apply List.mem_reverse.mp;rw [parts];exact List.mem_cons_self ..
  have member1 : second ∈ event.output.records := by apply List.mem_reverse.mp;rw [parts];exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have consumerMember : consumer0 ∈ event.output.records := by
    apply List.mem_reverse.mp;rw [parts]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  rcases schedule with ⟨eventBlock,indices,state0,state1,state2,state3,state4,mark0,mark1,root0,root1,emitted0,emitted1⟩
  have empty : ∀ record ∈ event.output.records,record.input.sunk[record.inst]! = true →
      record.output.state = record.input ∧ record.output.emitted = #[] := by
    intro record member marked
    have actual := ScansSpec.record_run (runScans_spec (stock_lower_event_scan_run run events)) record member
    have equal := Except.ok.inj (actual.symm.trans (scan_sunk event.ctx event.block record.inst event.termInst event.isBranch record.input marked))
    exact ⟨congrArg Scan.state equal,congrArg Scan.emitted equal⟩
  have marked0 : first.input.sunk[first.inst]! = true := by simpa only [parts,List.getElem!_cons_zero,pos0] using mark0
  have marked1 : second.input.sunk[second.inst]! = true := by simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ,pos1] using mark1
  obtain ⟨equal0,empty0⟩ := empty first member0 marked0
  obtain ⟨equal1,empty1⟩ := empty second member1 marked1
  have firstState : first.output.state = event.output.state := by simpa only [parts,List.getElem!_cons_zero] using state0
  have secondState : second.output.state = first.input := by simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using state1
  have consumerState : consumer0.output.state = second.input := by simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using state2
  have entryState : consumer0.output.state = event.output.state := consumerState.trans
    (equal1.symm.trans (secondState.trans (equal0.symm.trans firstState)))
  have selected : consumer0.output.step.map (·.rules.getLast?) = some (some 810) := by
    simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using root0
  have emitted : consumer0.output.step.map (·.decision) = some .emitted := by
    simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using emitted0
  obtain ⟨step,recorded,root,decision⟩ : ∃ step : Step,consumer0.output.step = some step ∧ step.rules.getLast? = some 810 ∧ step.decision = .emitted := by
    cases found : consumer0.output.step with
    | none => simp only [found,Option.map_none] at selected;cases selected
    | some step => exact ⟨step,rfl,Option.some.inj (by simpa only [found,Option.map_some] using selected),
        Option.some.inj (by simpa only [found,Option.map_some] using emitted)⟩
  obtain ⟨groups,frontiers,exactSunk,assembly⟩ := stock_lower_event_record_frontiers run events
  refine ⟨consumer0,step,consumer1.output.emitted++terminal.output.emitted,consumerMember,pos2,recorded,root,decision,entryState,?_⟩
  apply Array.toList_inj.mp
  simp only [assembly,parts,List.flatMap_cons,List.flatMap_nil,empty0,empty1,Array.toList_empty,
    List.nil_append,List.append_nil,Array.toList_append,List.append_assoc]

end Backend.Stock.Proof.AcquireTwoLoadPrefix
