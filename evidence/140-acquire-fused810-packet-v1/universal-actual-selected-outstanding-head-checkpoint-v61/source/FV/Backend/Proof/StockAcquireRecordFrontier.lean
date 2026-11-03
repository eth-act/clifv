import FV.Backend.Proof.StockAcquireWholeScanQueue

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

/-- Each record retains its actual interpreter frontier, or an empty update with unchanged marks. -/
def RecordFrontier (f : Clif.Function) (ctx : Ctx) (record : ScanRecord) (pending : List Nat) : Prop :=
  record.output.state.sunk = pending.foldl (fun bits producer => bits.set! producer true) record.input.sunk ∧
  (∀ producer ∈ pending,OriginalPendingSource f producer) ∧
  ((∃ step,record.output.step = some step ∧ step.decision = .emitted ∧
    PendingMarks ctx (scanState record.input record.inst) pending record.output.state) ∨
    (pending = [] ∧ record.output.state.sunk = record.input.sunk))

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

/-- Actual selection derives each record frontier; no caller supplies an interpreter trace. -/
theorem stock_lower_record_frontier {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records) :
    ∃ pending,RecordFrontier f event.ctx record pending := by
  have actual := scans_execute (runScans_spec (stock_lower_event_scan_run run events)) record records
  have emitted (actual : (emitInstruction event.ctx record.inst (scanState record.input record.inst) >>= fun emission =>
      pure (emission.scan event.block record.inst (scanState record.input record.inst))) = .ok record.output) :
      ∃ pending,RecordFrontier f event.ctx record pending := by
    obtain ⟨emission,called,finished⟩ := bind_success actual
    have outputEq : emission.scan event.block record.inst (scanState record.input record.inst) = record.output :=
      Except.ok.inj finished
    let step : Step := ⟨event.block,record.inst,.emitted,scanState record.input record.inst,emission.state,
      emission.results,emission.rules,emission.code⟩
    have recorded : record.output.step = some step := by rw [← outputEq]; rfl
    obtain ⟨original,ranges,initial,pending,built,func,marks,exactSunk,sources⟩ :=
      stock_lower_record_pending_mark_sources run events records recorded (by rfl)
    refine ⟨pending,exactSunk,?_,Or.inl ⟨step,recorded,rfl,marks⟩⟩
    intro producer member
    exact ⟨original,ranges,initial,built,sources producer member⟩
  unfold scanInstruction at actual
  dsimp only at actual
  generalize mandatoryEq : (if record.inst == event.termInst then true else event.ctx.insts[record.inst]!.clif.any mustLower) = mandatory at actual
  split at actual
  · exact ⟨[],by rw [← Except.ok.inj actual]; rfl,by simp,Or.inr ⟨rfl,by rw [← Except.ok.inj actual]⟩⟩
  · split at actual
    · exact ⟨[],by rw [← Except.ok.inj actual]; exact scanState_sunk _ _,by simp,
          Or.inr ⟨rfl,by rw [← Except.ok.inj actual]; exact scanState_sunk _ _⟩⟩
    · split at actual
      · exact ⟨[],by rw [← Except.ok.inj actual]; exact scanState_sunk _ _,by simp,
          Or.inr ⟨rfl,by rw [← Except.ok.inj actual]; exact scanState_sunk _ _⟩⟩
      · split at actual
        · obtain ⟨choice,committed,done⟩ := bind_success actual
          cases choice with
          | none => exact emitted done
          | some next =>
            have outputEq := Except.ok.inj done
            have kept : record.output.state.sunk = record.input.sunk := by
              rw [← outputEq]
              exact (opportunistic_sunk committed).trans (scanState_sunk _ _)
            exact ⟨[],kept,by simp,Or.inr ⟨rfl,kept⟩⟩
        · exact emitted actual

end Backend.Stock.Proof.Acquire810
