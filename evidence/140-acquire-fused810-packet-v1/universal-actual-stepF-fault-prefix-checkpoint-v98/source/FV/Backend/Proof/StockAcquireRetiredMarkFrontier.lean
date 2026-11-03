import FV.Backend.Proof.StockAcquireConsumerFreshMark

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A retired capture keeps its actual compiler mark absent at the current forward boundary. -/
def RetiredReadUnmarked {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    (frontier : ReadEffectFrontier ctx env program) (state : State) : Prop :=
  ∀ captured ∈ frontier.retired,state.sunk[captured.record.inst]! = false

/-- Every actual forward record preserves absence of marks already retired. -/
theorem stock_lower_retired_marks_progress {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {env : Clif.Env} {program : Clif.Program} {frontier : ReadEffectFrontier event.ctx env program}
    (retired : RetiredReadUnmarked frontier record.output.state) : RetiredReadUnmarked frontier record.input := by
  obtain ⟨pending,marks,monotone,sources⟩ := stock_lower_record_all_source_sunk_updates run events records
  intro captured member
  have absent := retired captured member
  cases marked : record.input.sunk[captured.record.inst]! with
  | false => rfl
  | true =>
    have impossible := monotone captured.record.inst marked
    rw [absent] at impossible
    cases impossible

/-- The real consumer retires its exact producer with an internally proved absent input mark. -/
theorem stock_lower_acquire_retired_marks {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record)
    {env : Clif.Env} {program : Clif.Program} (frontier : ReadEffectFrontier event.ctx env program)
    (captured : SunkReadSnapshot event.ctx env program) (tail : List (SunkReadSnapshot event.ctx env program))
    (head : frontier.pending = captured::tail) (producer : captured.record.inst = R.producer)
    (prior : RetiredReadUnmarked frontier record.output.state) :
    RetiredReadUnmarked (frontier.retire captured tail head) record.input := by
  have old := stock_lower_retired_marks_progress run events records prior
  intro actual member
  change actual ∈ frontier.retired++[captured] at member
  rcases List.mem_append.mp member with inherited | current
  · exact old actual inherited
  · have same := List.mem_singleton.mp current
    subst actual
    rw [producer]
    exact stock_lower_acquire_consumer_input_unmarked run scope events records recorded emitted selectedId R

/-- A still-marked actual capture cannot be hidden among retired history. -/
theorem marked_capture_pending {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    {frontier : ReadEffectFrontier ctx env program} {state : State} {captured : SunkReadSnapshot ctx env program}
    (member : captured ∈ frontier.history) (marked : state.sunk[captured.record.inst]! = true)
    (retired : RetiredReadUnmarked frontier state) : captured ∈ frontier.pending := by
  rw [frontier.split] at member
  rcases List.mem_append.mp member with past | pending
  · have impossible := retired captured past
    rw [impossible] at marked
    cases marked
  · exact pending

/-- The actual selected source capture belongs to the outstanding frontier, not retired history. -/
theorem stock_lower_acquire_selected_capture_pending {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record)
    {env : Clif.Env} {program : Clif.Program} {frontier : ReadEffectFrontier event.ctx env program}
    {captured : SunkReadSnapshot event.ctx env program}
    (member : captured ∈ frontier.history) (producer : captured.record.inst = R.producer)
    (retired : RetiredReadUnmarked frontier record.output.state) : captured ∈ frontier.pending := by
  apply marked_capture_pending member ?_ retired
  rw [producer]
  exact stock_lower_acquire_output_producer_marked run scope events records recorded emitted selectedId R

end Backend.Stock.Proof.Acquire810
