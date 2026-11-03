import FV.Backend.Proof.StockAcquireEntryPendingExhaustion
import FV.Backend.Proof.StockReturnRecordCalls
import FV.Backend.Proof.StockTerminalEmission

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- The actual retained return record starts in the event's original scan input. -/
theorem stock_lower_return_record_input {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    (terminal : record.inst = event.termInst) : record.input = event.input := by
  obtain ⟨block,term,body,split⟩ := stock_lower_body_scan_split run scope events
  rw [split.records] at records
  rcases List.mem_cons.mp records with rfl | member
  · exact split.termInput
  · obtain ⟨j,stm,statement,current⟩ := split.positions record member
    have bound : j < block.body.length := by
      by_cases bound : j < block.body.length
      · exact bound
      · rw [List.getElem?_eq_none (Nat.le_of_not_lt bound)] at statement
        cases statement
    rw [terminal,split.termIndex] at current
    omega

/-- The real return helper changes demand and emits rets while preserving every inherited sink mark. -/
theorem stock_lower_return_record_sunk {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {block : Clif.Block} (blockAt : f.blocks[event.block]? = some block)
    {values : List Nat} (ret : block.term = .ret values)
    {record : ScanRecord} (records : record ∈ event.output.records)
    (terminal : record.inst = event.termInst) : record.output.state.sunk = event.input.sunk := by
  obtain ⟨step,recorded,emitted⟩ := stock_lower_retTrap_record_emitted run scope events blockAt
    (by rw [ret];rfl) records terminal
  obtain ⟨fuel,trace,rs,ps,enough,helper,root,mapped,pinned,state,chunk⟩ :=
    stock_lower_return_record_helper run scope events blockAt ret records terminal recorded emitted
  have marks : ∀ (xs : List Nat) (before : State),(xs.foldl State.mark before).sunk = before.sunk := by
    intro xs before
    induction xs generalizing before with
    | nil => rfl
    | cons x xs ih => exact ih (before.mark x)
  rw [state]
  change ((values++sretRet f).foldl State.mark (scanState record.input record.inst)).sunk = event.input.sunk
  rw [marks]
  rw [scanState_sunk]
  rw [stock_lower_return_record_input run scope events records terminal]

/-- The actual before-return compiler state exhausts pending reads without a caller empty-frontier certificate. -/
theorem stock_lower_return_pending_exhausted {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {block : Clif.Block} (blockAt : f.blocks[event.block]? = some block)
    {values : List Nat} (ret : block.term = .ret values)
    {record : ScanRecord} (records : record ∈ event.output.records)
    (terminal : record.inst = event.termInst)
    {env : Clif.Env} {program : Clif.Program} (frontier : ReadEffectFrontier event.ctx env program)
    (retained : ∀ captured ∈ frontier.history,captured.record ∈ event.output.records)
    (marked : PendingReadMarks frontier record.output.state) : frontier.pending = [] := by
  apply stock_lower_entry_pending_exhausted run scope events frontier retained
  intro captured member
  have actual := marked captured member
  rwa [stock_lower_return_record_sunk run scope events blockAt ret records terminal] at actual

/-- Before the actual return chunk, the complete paired frontier recovers every demanded binding in both worlds. -/
theorem stock_lower_paired_return_guarded_recovery {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {block : Clif.Block} (blockAt : f.blocks[event.block]? = some block)
    {values : List Nat} (ret : block.term = .ret values)
    {record : ScanRecord} (records : record ∈ event.output.records)
    (terminal : record.inst = event.termInst)
    {env : Clif.Env} {program : Clif.Program} {MR : MemRelT} {Z : BitVec 64 → Prop}
    {entry : Clif.Frame × Clif.Mem} {prefixRecords : List ScanRecord} {point : SourcePoint}
    {regs : Nat → CV} {worlds : W2}
    (prior : PairedReadFrontierAt f result event env program MR Z entry prefixRecords record.output.state point regs worlds) :
    prior.frontier.pending = [] ∧
      GuardedScanRel f result event.ctx event.block MR record.output.state point regs worlds.1 ∧
      GuardedScanRel f result event.ctx event.block MR record.output.state point regs worlds.2 ∧
      SameWorld Z worlds.1 worlds.2 := by
  have finished := stock_lower_return_pending_exhausted run scope events blockAt ret records terminal
    prior.frontier prior.retained prior.pending
  exact ⟨finished,frontier_final_guarded prior.left prior.retiredValues finished,
    frontier_final_guarded prior.right prior.retiredValues finished,prior.agreement⟩

end Backend.Stock.Proof.Acquire810
