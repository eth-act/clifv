import FV.Backend.Proof.StockAcquireActualScanMarks
import FV.Backend.Proof.StockAcquireScanAssembly

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

/-- Membership in the original source effect list, derived from the actual retained records. -/
def OriginalPendingSource (f : Clif.Function) (producer : Nat) : Prop :=
  ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState),
    Backend.buildCtx f = .ok (original,ranges,initial) ∧
    some producer ∈ sourceColorEvents original ranges

private def SourceDelta (f : Clif.Function) (before after : State) : Prop :=
  ∃ pending : List Nat,
    after.sunk = pending.foldl (fun bits producer => bits.set! producer true) before.sunk ∧
    (∀ target : Nat,before.sunk[target]! = true → after.sunk[target]! = true) ∧
    ∀ producer ∈ pending,OriginalPendingSource f producer

private theorem delta_same {f : Clif.Function} {before after : State} (sunk : after.sunk = before.sunk) :
    SourceDelta f before after :=
  ⟨[],sunk,(fun target marked => by rwa [sunk]),by simp⟩

private theorem delta_trans {f : Clif.Function} {before middle after : State}
    (first : SourceDelta f before middle) (second : SourceDelta f middle after) : SourceDelta f before after := by
  obtain ⟨left,first,firstMono,firstSources⟩ := first
  obtain ⟨right,second,secondMono,secondSources⟩ := second
  refine ⟨left++right,?_,fun target marked => secondMono target (firstMono target marked),?_⟩
  · rw [List.foldl_append,← first]
    exact second
  · intro producer member
    rcases List.mem_append.mp member with member | member
    · exact firstSources producer member
    · exact secondSources producer member

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

/-- Every real scan decision derives its sink updates and original source membership. -/
theorem stock_lower_record_all_source_sunk_updates {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records) :
    ∃ pending : List Nat,
      record.output.state.sunk = pending.foldl (fun bits producer => bits.set! producer true) record.input.sunk ∧
      (∀ target : Nat,record.input.sunk[target]! = true → record.output.state.sunk[target]! = true) ∧
      ∀ producer ∈ pending,OriginalPendingSource f producer := by
  change SourceDelta f record.input record.output.state
  have actual := scans_execute (runScans_spec (stock_lower_event_scan_run run events)) record records
  have reset : SourceDelta f record.input (scanState record.input record.inst) :=
    delta_same (scanState_sunk record.input record.inst)
  have emitted (actual : (emitInstruction event.ctx record.inst (scanState record.input record.inst) >>= fun emission =>
      pure (emission.scan event.block record.inst (scanState record.input record.inst))) = .ok record.output) :
      SourceDelta f record.input record.output.state := by
    obtain ⟨emission,called,finished⟩ := bind_success actual
    have outputEq : emission.scan event.block record.inst (scanState record.input record.inst) = record.output :=
      Except.ok.inj finished
    let step : Step := ⟨event.block,record.inst,.emitted,scanState record.input record.inst,emission.state,
      emission.results,emission.rules,emission.code⟩
    have recorded : record.output.step = some step := by rw [← outputEq]; rfl
    obtain ⟨original,ranges,initial,pending,built,func,marks,exactSunk,sources⟩ :=
      stock_lower_record_pending_mark_sources run events records recorded (by rfl)
    refine ⟨pending,exactSunk,?_,?_⟩
    · intro target marked
      apply marks.marked_mono target
      rwa [scanState_sunk]
    · intro producer member
      exact ⟨original,ranges,initial,built,sources producer member⟩
  unfold scanInstruction at actual
  dsimp only at actual
  generalize mandatoryEq : (if record.inst == event.termInst then true else event.ctx.insts[record.inst]!.clif.any mustLower) = mandatory at actual
  split at actual
  · rw [← Except.ok.inj actual]; exact delta_same rfl
  · split at actual
    · rw [← Except.ok.inj actual]; exact reset
    · split at actual
      · rw [← Except.ok.inj actual]; exact reset
      · split at actual
        · obtain ⟨choice,committed,done⟩ := bind_success actual
          cases choice with
          | none => exact emitted done
          | some next =>
            have outputEq := Except.ok.inj done
            rw [← outputEq]
            exact delta_trans reset (delta_same (opportunistic_sunk committed))
        · exact emitted actual

private theorem scans_delta {f : Clif.Function} {exec : Nat → State → Except String Scan}
    {indices : List Nat} {before : State} {output : BlockScan}
    (spec : ScansSpec exec indices before output)
    (recordDelta : ∀ record ∈ output.records,SourceDelta f record.input record.output.state) :
    SourceDelta f before output.state := by
  revert recordDelta
  induction spec with
  | nil => intro recordDelta; exact delta_same rfl
  | cons head tail ih =>
    intro recordDelta
    exact delta_trans (recordDelta _ (List.mem_cons_self ..))
      (ih (fun record member => recordDelta record (List.mem_cons_of_mem _ member)))

/-- The complete actual scan derives its general source queue and exact mark updates. -/
theorem stock_lower_event_source_sunk_updates {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) :
    ∃ pending : List Nat,
      event.output.state.sunk = pending.foldl (fun bits producer => bits.set! producer true) event.input.sunk ∧
      (∀ target : Nat,event.input.sunk[target]! = true → event.output.state.sunk[target]! = true) ∧
      ∀ producer ∈ pending,OriginalPendingSource f producer := by
  change SourceDelta f event.input event.output.state
  apply scans_delta (runScans_spec (stock_lower_event_scan_run run events))
  intro record records
  exact stock_lower_record_all_source_sunk_updates run events records

end Backend.Stock.Proof.Acquire810
