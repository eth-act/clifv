import FV.Backend.Proof.StockAcquireOpportunisticMarks

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

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
    cases called : emitInstruction event.ctx record.inst (scanState record.input record.inst) with
    | error message => simp only [called,bind,Except.bind] at actual; cases actual
    | ok emission =>
      simp only [called,bind,Except.bind,pure,Except.pure] at actual
      have outputEq := Except.ok.inj actual
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
  · cases actual; exact delta_same rfl
  · split at actual
    · cases actual; exact reset
    · split at actual
      · cases actual; exact reset
      · split at actual
        · cases committed : commitOpportunistic event.ctx event.block record.inst (scanState record.input record.inst) with
          | error message => simp only [committed,bind,Except.bind] at actual; cases actual
          | ok result =>
            simp only [committed,bind,Except.bind] at actual
            cases result with
            | none => exact emitted actual
            | some next =>
              cases actual
              exact delta_trans reset (delta_same (opportunistic_sunk committed))
        · exact emitted actual

private theorem scans_delta {exec : Nat → State → Except String Scan}
    {indices : List Nat} {before : State} {output : BlockScan}
    (spec : ScansSpec exec indices before output)
    (recordDelta : ∀ record ∈ output.records,SunkDelta record.input record.output.state) :
    SunkDelta before output.state := by
  revert recordDelta
  induction spec with
  | nil => intro recordDelta; exact delta_same rfl
  | cons head tail ih =>
    intro recordDelta
    exact delta_trans (recordDelta _ (List.mem_cons_self ..))
      (ih (fun record member => recordDelta record (List.mem_cons_of_mem _ member)))

/-- The complete actual source scan composes every sink update and preserves prior marks. -/
theorem stock_lower_event_sunk_updates {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) :
    ∃ pending : List Nat,
      event.output.state.sunk = pending.foldl (fun bits producer => bits.set! producer true) event.input.sunk ∧
      ∀ target : Nat,event.input.sunk[target]! = true → event.output.state.sunk[target]! = true := by
  change SunkDelta event.input event.output.state
  apply scans_delta (runScans_spec (stock_lower_event_scan_run run events))
  intro record records
  exact stock_lower_record_all_sunk_updates run events records

end Backend.Stock.Proof.Acquire810
