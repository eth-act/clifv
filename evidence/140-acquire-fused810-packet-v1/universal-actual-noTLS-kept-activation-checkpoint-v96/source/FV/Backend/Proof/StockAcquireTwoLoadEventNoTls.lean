import FV.Backend.Proof.StockAcquireAssemblyNoTls
import FV.Backend.Proof.StockAcquireTwoLoadRecords
import FV.Backend.Proof.StockAcquireSelectedChunk
import FV.Backend.Proof.StockReturnRecordCalls
import FV.Backend.Proof.StockTerminalEmission

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- Real selected consumers emit only the acquire and introduce no TLS instruction. -/
theorem selected_acquire_no_tls {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selected : step.rules.getLast? = some 810) :
    ∀ inst ∈ record.output.emitted.toList,NoTlsInst inst := by
  obtain ⟨R,pointer,dest,value,key,held,results,resultReg,fresh,chunk,rest⟩ :=
    stock_lower_acquire_selected_chunk run scope dominated events records recorded emitted selected
  intro inst member
  rw [chunk] at member
  simp only [List.mem_singleton] at member
  subst inst
  trivial

/-- Actual retained records derive the complete event's absence of TLS, including both sunk producers. -/
theorem two_load_event_no_tls {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function) (dominated : Dominated function)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) (schedule : ActualSchedule event) :
    ∀ inst ∈ event.output.code.toList,NoTlsInst inst := by
  obtain ⟨records⟩ := actual_two_load_records run scope dominated events schedule
  have empty : ∀ record ∈ event.output.records,record.input.sunk[record.inst]! = true → record.output.emitted = #[] := by
    intro record member marked
    have actual := ScansSpec.record_run (runScans_spec (stock_lower_event_scan_run run events)) record member
    exact congrArg Scan.emitted (Except.ok.inj (actual.symm.trans
      (scan_sunk event.ctx event.block record.inst event.termInst event.isBranch record.input marked)))
  have empty0 := empty records.first (records.member _ (by simp)) records.marked0
  have empty1 := empty records.second (records.member _ (by simp)) records.marked1
  have consumer0 := selected_acquire_no_tls run scope dominated events
    (records.member _ (by simp)) records.recorded0 records.emitted0 records.selected0
  have consumer1 := selected_acquire_no_tls run scope dominated events
    (records.member _ (by simp)) records.recorded1 records.emitted1 records.selected1
  have block : function.blocks[event.block]? = some function.blocks[0]! := by rw [schedule.1];rfl
  obtain ⟨original,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have blockEq := Option.some.inj (split.block.symm.trans block)
  subst original
  have terminalIndex : event.termInst = 4 := by
    simpa [schedule.1,function,blockStart] using split.termIndex
  have terminal : records.terminal.inst = event.termInst := records.pos4.trans terminalIndex.symm
  obtain ⟨step,recorded,emitted⟩ := stock_lower_retTrap_record_emitted run scope events block
    (by rfl) (records.member _ (by simp)) terminal
  obtain ⟨fuel,trace,rs,ps,enough,helper,root,mapped,pinned,state,chunk⟩ :=
    stock_lower_return_record_helper run scope events block (by rfl)
      (records.member _ (by simp)) terminal recorded emitted
  have lastNoCall : ∀ inst ∈ records.terminal.output.emitted.toList,NoTlsInst inst := by
    intro inst member
    rw [chunk] at member
    simp only [List.mem_singleton] at member
    subst inst
    trivial
  obtain ⟨groups,frontiers,exactSunk,assembly⟩ := stock_lower_event_record_frontiers run events
  intro inst member
  rw [assembly,records.parts] at member
  simp only [List.flatMap_cons,List.flatMap_nil,empty0,empty1,Array.toList_empty,List.nil_append,List.append_nil,
    List.mem_append] at member
  rcases member with member | member | member
  · exact consumer0 inst member
  · exact consumer1 inst member
  · exact lastNoCall inst member

end Backend.Stock.Proof.AcquireTwoLoadPrefix
