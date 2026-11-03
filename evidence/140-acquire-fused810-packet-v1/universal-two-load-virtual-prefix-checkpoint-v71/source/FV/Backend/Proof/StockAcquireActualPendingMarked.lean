import FV.Backend.Proof.StockAcquireDriverSunkSize

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The real initializer gives mark and metadata arrays exactly the same extent. -/
theorem buildCtx_sunk_color_extent {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (built : Stock.buildCtx f = .ok (ctx,ranges,initial)) : initial.sunk.size = initial.entryColor.size := by
  obtain ⟨original,oldState,requests,oldBuild,allocation,finished⟩ := buildCtx_allocation built
  have marks := congrArg (fun value : Ctx × Array (Nat × Nat) × State => value.2.2.sunk.size) finished
  have colors := congrArg (fun value : Ctx × Array (Nat × Nat) × State => value.2.2.entryColor.size) finished
  simp only [finishCtx,Array.size_replicate] at marks colors
  rw [sourceMetadata_color_events,color_events_size] at colors
  simp only [Array.size_replicate] at colors
  exact marks.trans colors.symm

/-- Actual retained inputs preserve the initializer's exact mark/metadata extent equality. -/
theorem stock_lower_record_sunk_color_extent {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records) :
    record.input.sunk.size = record.input.entryColor.size := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  have metadata := (((stock_lower_zeroColorLe run).2 event events).2 record records).1.1
  rw [stock_lower_record_sunk_extent run events records,metadata]
  exact buildCtx_sunk_color_extent build

/-- Every actual sink names a positive metadata entry, including later members of a general queue. -/
theorem PendingMarks.member_positive {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : PendingMarks ctx before pending after) {producer : Nat} (member : producer ∈ pending) :
    before.entryColor[producer]! ≠ 0 := by
  induction trace with
  | nil => cases member
  | @sink before middle after head rest actual tail ih =>
    rcases List.mem_cons.mp member with equal | member
    · subst head
      exact (sink_accepted actual).1
    · have positive := ih member
      rw [(sink_accepted actual).2.2.2.2] at positive
      exact positive
  | frame entries color sunk tail ih =>
    have positive := ih member
    rwa [entries] at positive

/-- Actual emitted pending groups mark every producer; all bounds come from the real initializer. -/
theorem stock_lower_record_read_pending_marked {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ pending,ReadPendingMarks event.ctx (scanState record.input record.inst) pending record.output.state ∧
      ∀ producer ∈ pending,record.output.state.sunk[producer]! = true := by
  obtain ⟨pending,trace,exactSunk,frames⟩ := stock_lower_record_read_pending_marks run events records recorded emitted
  refine ⟨pending,trace,?_⟩
  intro producer member
  have positive := trace.forget.member_positive member
  have inside : producer < (scanState record.input record.inst).entryColor.size := by
    apply Classical.byContradiction
    intro outside
    have absent := Array.getElem?_eq_none (Nat.le_of_not_lt outside)
    simp only [getElem!_def,absent] at positive
    exact positive rfl
  have size : (scanState record.input record.inst).sunk.size =
      (scanState record.input record.inst).entryColor.size := by
    unfold scanState
    dsimp only
    split <;> exact stock_lower_record_sunk_color_extent run events records
  exact trace.forget.member_marked (by rwa [size]) member

end Backend.Stock.Proof.Acquire810
