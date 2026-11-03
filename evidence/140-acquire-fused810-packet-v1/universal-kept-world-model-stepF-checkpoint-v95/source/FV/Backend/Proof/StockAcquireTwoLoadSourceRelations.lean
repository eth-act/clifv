import FV.Backend.Proof.StockAcquireTwoLoadActualSource
import FV.Backend.Proof.StockAcquireTwoLoadSchedule

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- Actual retained consumer metadata derives the original successful and faulting source relations.
No caller supplies either endpoint receipt or an event-context execution certificate. -/
theorem actual_two_load_source_relations {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function) (dominated : Dominated function)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) (schedule : ActualSchedule event)
    (env : Clif.Env) (program : Clif.Program) (firstPointer secondPointer : BitVec 64)
    (memory : Clif.Mem) (raw : BitVec 8) (code : Clif.TrapCode)
    (loaded : memory.load {} (Clif.effAddr ⟨.i64,firstPointer⟩ 0) 1 8 = .ok raw)
    (failed : memory.load {} (Clif.effAddr ⟨.i64,secondPointer⟩ 0) 1 8 = .trap code) :
    SourceInstResult env program event.ctx 0 (entry firstPointer secondPointer,memory)
      (afterFirst firstPointer secondPointer raw,memory) ∧
    SourceInstFault env program event.ctx 1 (afterFirst firstPointer secondPointer raw,memory) code := by
  obtain ⟨first,second,consumer0,consumer1,terminal,parts,pos0,pos1,pos2,pos3,pos4⟩ := actual_schedule_records schedule
  have member0 : consumer0 ∈ event.output.records := by
    apply List.mem_reverse.mp;rw [parts]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have member1 : consumer1 ∈ event.output.records := by
    apply List.mem_reverse.mp;rw [parts]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have choose : ∀ (record : ScanRecord),record.output.step.map (·.rules.getLast?) = some (some 810) →
      record.output.step.map (·.decision) = some .emitted →
      ∃ step : Step,record.output.step = some step ∧ step.rules.getLast? = some 810 ∧ step.decision = .emitted := by
    intro record root emitted
    cases found : record.output.step with
    | none => simp only [found,Option.map_none] at root;cases root
    | some step => exact ⟨step,rfl,Option.some.inj (by simpa only [found,Option.map_some] using root),
        Option.some.inj (by simpa only [found,Option.map_some] using emitted)⟩
  have root0 : consumer0.output.step.map (·.rules.getLast?) = some (some 810) := by
    simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using schedule.2.2.2.2.2.2.2.2.2.1
  have root1 : consumer1.output.step.map (·.rules.getLast?) = some (some 810) := by
    simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using schedule.2.2.2.2.2.2.2.2.2.2.1
  have emitted0 : consumer0.output.step.map (·.decision) = some .emitted := by
    simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using schedule.2.2.2.2.2.2.2.2.2.2.2.1
  have emitted1 : consumer1.output.step.map (·.decision) = some .emitted := by
    simpa only [parts,List.getElem!_cons_zero,List.getElem!_cons_succ] using schedule.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨step0,recorded0,selected0,decision0⟩ := choose consumer0 root0 emitted0
  obtain ⟨step1,recorded1,selected1,decision1⟩ := choose consumer1 root1 emitted1
  obtain ⟨R0⟩ := stock_lower_acquire_source_endpoint_receipt run scope dominated events member0 recorded0 decision0 selected0
  obtain ⟨R1⟩ := stock_lower_acquire_source_endpoint_receipt run scope dominated events member1 recorded1 decision1 selected1
  exact ⟨actual_first_source_result run scope events schedule.1 pos2 R0 env program firstPointer secondPointer memory raw loaded,
    actual_second_source_fault run scope events schedule.1 pos3 R1 env program firstPointer secondPointer memory raw code failed⟩

end Backend.Stock.Proof.AcquireTwoLoadPrefix
