import FV.Backend.Proof.StockAcquireOpportunisticMarks

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

private theorem bind_success {α β : Type} {value : Except String α}
    {next : α → Except String β} {output : β}
    (run : (value >>= next) = .ok output) :
    ∃ input,value = .ok input ∧ next input = .ok output := by
  cases value with
  | error message => cases run
  | ok input => exact ⟨input,rfl,run⟩

private def SunkDelta (before after : State) : Prop :=
  ∃ pending : List Nat,
    after.sunk = pending.foldl (fun bits producer => bits.set! producer true) before.sunk ∧
    ∀ target : Nat,before.sunk[target]! = true → after.sunk[target]! = true

private theorem delta_same {before after : State} (sunk : after.sunk = before.sunk) :
    SunkDelta before after := ⟨[],sunk,fun target marked => by rwa [sunk]⟩

private theorem delta_trans {before middle after : State}
    (first : SunkDelta before middle) (second : SunkDelta middle after) : SunkDelta before after := by
  obtain ⟨left,first,firstMono⟩ := first
  obtain ⟨right,second,secondMono⟩ := second
  refine ⟨left++right,?_,fun target marked => secondMono target (firstMono target marked)⟩
  rw [List.foldl_append,← first]
  exact second

private theorem scans_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (spec : ScansSpec exec indices input output) :
    ∀ record ∈ output.records,exec record.inst record.input = .ok record.output := by
  induction spec with
  | nil input => simp
  | cons head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member

/-- Every retained event contains the actual successful scan, including all real decision paths. -/
theorem stock_lower_event_scan_run {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) :
    scanBlock event.ctx event.block event.termInst event.isBranch event.indices event.input = .ok event.output := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,nodeIndex,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  rw [eventEq]
  exact (stock_lowerBlockCore_scanOrigin coreRun).2.2.2.2.2

/-- Every real scan decision derives its complete sink updates without a standalone emitter certificate. -/
theorem stock_lower_record_all_sunk_updates {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records) :
    ∃ pending : List Nat,
      record.output.state.sunk = pending.foldl (fun bits producer => bits.set! producer true) record.input.sunk ∧
      ∀ target : Nat,record.input.sunk[target]! = true → record.output.state.sunk[target]! = true := by
  change SunkDelta record.input record.output.state
  have actual := scans_execute (runScans_spec (stock_lower_event_scan_run run events)) record records
  have reset : SunkDelta record.input (scanState record.input record.inst) :=
    delta_same (scanState_sunk record.input record.inst)
  have emitted (actual : (emitInstruction event.ctx record.inst (scanState record.input record.inst) >>= fun emission =>
      pure (emission.scan event.block record.inst (scanState record.input record.inst))) = .ok record.output) :
      SunkDelta record.input record.output.state := by
    obtain ⟨emission,called,finished⟩ := bind_success actual
    have outputEq : emission.scan event.block record.inst (scanState record.input record.inst) = record.output :=
      Except.ok.inj finished
    let step : Step := ⟨event.block,record.inst,.emitted,scanState record.input record.inst,emission.state,
      emission.results,emission.rules,emission.code⟩
    have recorded : record.output.step = some step := by rw [← outputEq]; rfl
    obtain ⟨pending,marks,exactSunk,monotone⟩ :=
      stock_lower_record_pending_marks run events records recorded (by rfl)
    exact ⟨pending,exactSunk,monotone⟩
  unfold scanInstruction at actual
  dsimp only at actual
  generalize mandatoryEq : (if record.inst == event.termInst then true else event.ctx.insts[record.inst]!.clif.any mustLower) = mandatory at actual
  split at actual
  all_goals trace_state

end Backend.Stock.Proof.Acquire810
