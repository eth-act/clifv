import FV.Backend.Proof.StockAcquireTwoLoadReturnedSourceSteps

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false

/-- Complete actual source history and final compiler marks derive exhaustion of the two-load frontier. -/
theorem two_load_completed_frontier_empty {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) (entryBlock : event.block = 0)
    (records : TwoLoadRecords event) {env : Clif.Env} {program : Clif.Program}
    {before after : Clif.Frame × Clif.Mem} {frontier : ReadEffectFrontier event.ctx env program}
    (history : SourceReadCaptures event.ctx env program (event.output.records.reverse.take 4) before after frontier.history)
    (pending : PendingReadMarks frontier records.terminal.output.state) : frontier.pending = [] := by
  have member0 := records.member records.consumer0 (by simp)
  have member1 := records.member records.consumer1 (by simp)
  obtain ⟨pi0,ci0,producer0,value0,pointer0,ty0,flags0⟩ := first_consumer_endpoints entryBlock records.pos2 records.R0
  obtain ⟨pi1,ci1,producer1,value1,pointer1,ty1,flags1⟩ := second_consumer_endpoints entryBlock records.pos3 records.R1
  have unmarked0 := stock_lower_emitted_record_unsunk run events member0 records.recorded0 records.emitted0
  have unmarked1 := stock_lower_emitted_record_unsunk run events member1 records.recorded1 records.emitted1
  have retired0 : records.consumer0.input.sunk[0]! = false := by
    simpa only [producer0] using stock_lower_acquire_consumer_input_unmarked run scope events member0 records.recorded0 records.emitted0 records.selected0 records.R0
  have prior0 : records.consumer1.output.state.sunk[0]! = false := by rw [records.consumer1State];exact retired0
  obtain ⟨updates,marks,monotone,sources⟩ := stock_lower_record_all_source_sunk_updates run events member1
  have final0 : records.consumer1.input.sunk[0]! = false := by
    cases marked : records.consumer1.input.sunk[0]! with
    | false => rfl
    | true => have impossible := monotone 0 marked;rw [prior0] at impossible;cases impossible
  have final1 : records.consumer1.input.sunk[1]! = false := by
    simpa only [producer1] using stock_lower_acquire_consumer_input_unmarked run scope events member1 records.recorded1 records.emitted1 records.selected1 records.R1
  cases pendingEq : frontier.pending with
  | nil => rfl
  | cons captured rest =>
    have member : captured ∈ frontier.pending := by rw [pendingEq];exact List.mem_cons_self ..
    have historyMember : captured ∈ frontier.history := by rw [frontier.split];exact List.mem_append_right _ member
    have original := history.record_membership captured historyMember
    simp only [records.parts,List.take_succ_cons,List.take_zero,List.mem_cons,List.not_mem_nil,or_false] at original
    have sourcePosition : captured.record.inst = 0 ∨ captured.record.inst = 1 := by
      rcases original with equal | equal | equal | equal
      · exact .inl (congrArg ScanRecord.inst equal |>.trans records.pos0)
      · exact .inr (congrArg ScanRecord.inst equal |>.trans records.pos1)
      · have marked := captured.marked;rw [equal,unmarked0] at marked;cases marked
      · have marked := captured.marked;rw [equal,unmarked1] at marked;cases marked
    have marked := pending captured member
    rw [records.terminalState] at marked
    rcases sourcePosition with first | second
    · rw [first,final0] at marked;cases marked
    · rw [second,final1] at marked;cases marked

/-- Final recovery retains every original demanded binding after the actual completed source prefix. -/
theorem two_load_completed_guarded_recovery {result : Result}
    (run : Stock.lower function = .ok result) (scope : LowerScope function)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) (entryBlock : event.block = 0)
    (records : TwoLoadRecords event) {env : Clif.Env} {program : Clif.Program} {MR : MemRelT}
    {before after : Clif.Frame × Clif.Mem} {frontier : ReadEffectFrontier event.ctx env program}
    {regs : Nat → CV} {world : Arm.ArmState}
    (history : SourceReadCaptures event.ctx env program (event.output.records.reverse.take 4) before after frontier.history)
    (pending : PendingReadMarks frontier records.terminal.output.state)
    (retired : RetiredUndemanded frontier records.terminal.output.state)
    (related : PendingGuardedScanRel function result event.ctx event.block env program MR frontier.history
      records.terminal.output.state (4,after) regs world) :
    GuardedScanRel function result event.ctx event.block MR records.terminal.output.state (4,after) regs world := by
  exact frontier_final_guarded related retired (two_load_completed_frontier_empty run scope events entryBlock records history pending)

end Backend.Stock.Proof.AcquireTwoLoadPrefix
