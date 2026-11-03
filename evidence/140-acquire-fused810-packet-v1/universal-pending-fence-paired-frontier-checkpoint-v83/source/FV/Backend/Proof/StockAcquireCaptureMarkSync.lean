import FV.Backend.Proof.StockAcquireActualFaultCaptures
import FV.Backend.Proof.StockSSAScanConnection

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual block construction derives unique original source indices. -/
theorem stock_lower_event_source_indices_nodup {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    event.indices.Nodup := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,nodeBi,data,core,build,ordered,
    initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨_,_,_,_,indicesEq,_⟩ := stock_lowerBlockCore_scanOrigin coreRun
  rw [eventEq,indicesEq]
  exact stock_scan_indices_nodup _ _

/-- The actual retained records inherit unique source indices from construction. -/
theorem stock_lower_event_record_indices_nodup {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    (event.output.records.map (·.inst)).Nodup := by
  rw [(runScans_spec (stock_lower_event_scan_run run events)).order]
  exact stock_lower_event_source_indices_nodup run events

/-- Exact capture histories retain the source list's original index uniqueness. -/
theorem SourceReadCaptures.slot_nodup {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    {records : List ScanRecord} {before after : Clif.Frame × Clif.Mem}
    {captures : List (SunkReadSnapshot ctx env program)} (trace : SourceReadCaptures ctx env program records before after captures)
    (unique : (records.map (·.inst)).Nodup) : (captures.map (fun captured => captured.record.inst)).Nodup := by
  rw [trace.marked_slots]
  exact unique.sublist (List.filter_sublist.map (fun record : ScanRecord => record.inst))

/-- Every actual finite source prefix derives capture uniqueness internally. -/
theorem stock_lower_actual_prefix_capture_indices_nodup {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {count : Nat} {env : Clif.Env} {program : Clif.Program} {before after : Clif.Frame × Clif.Mem}
    {captures : List (SunkReadSnapshot event.ctx env program)}
    (trace : SourceReadCaptures event.ctx env program (event.output.records.reverse.take count) before after captures) :
    (captures.map (fun captured => captured.record.inst)).Nodup := by
  have records := stock_lower_event_record_indices_nodup run events
  have forward : (event.output.records.reverse.map (·.inst)).Nodup := by
    rw [List.map_reverse]
    apply List.pairwise_reverse.mpr
    exact records.imp (fun different same => different same.symm)
  exact trace.slot_nodup (forward.sublist ((List.take_sublist count event.output.records.reverse).map (fun record => record.inst)))

/-- Actual retained selection changes exactly one sink mark, not an external effect summary. -/
theorem stock_lower_acquire_sunk_delta {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record) :
    record.output.state.sunk = record.input.sunk.set! R.producer true := by
  obtain ⟨pending,frontier⟩ := stock_lower_record_executed_frontier run events records
  have singleton := executed_frontier_acquire_singleton run scope events records recorded emitted selectedId R frontier
  simpa only [singleton,List.foldl_cons,List.foldl_nil] using frontier.1.1

/-- The outstanding frontier keeps the actual compiler marks synchronized. -/
def PendingReadMarks {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    (frontier : ReadEffectFrontier ctx env program) (state : State) : Prop :=
  ∀ captured ∈ frontier.pending,state.sunk[captured.record.inst]! = true

/-- Actual consumer mark removal preserves every other outstanding producer's mark. -/
theorem stock_lower_acquire_pending_marks_retire {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record)
    {env : Clif.Env} {program : Clif.Program} (frontier : ReadEffectFrontier event.ctx env program)
    (captured : SunkReadSnapshot event.ctx env program) (tail : List (SunkReadSnapshot event.ctx env program))
    (head : frontier.pending = captured::tail) (producer : captured.record.inst = R.producer)
    (unique : (frontier.pending.map (fun actual => actual.record.inst)).Nodup)
    (marked : PendingReadMarks frontier record.output.state) :
    PendingReadMarks (frontier.retire captured tail head) record.input := by
  have delta := stock_lower_acquire_sunk_delta run scope events records recorded emitted selectedId R
  rw [head,List.map_cons,List.nodup_cons] at unique
  intro actual member
  change actual ∈ tail at member
  have prior := marked actual (by rw [head];exact List.mem_cons_of_mem _ member)
  have different : actual.record.inst ≠ R.producer := by
    intro same
    apply unique.1
    apply List.mem_map.mpr
    exact ⟨actual,member,same.trans producer.symm⟩
  rw [delta,getElem!_def,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_ne (Ne.symm different)] at prior
  simpa only [getElem!_def] using prior

end Backend.Stock.Proof.Acquire810
