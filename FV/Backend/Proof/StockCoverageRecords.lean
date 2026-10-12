import FV.Backend.Proof.StockCoverageDriver

/-! Eliminate remembered-definition scan decisions at actual whole-driver records. -/
namespace Backend.Stock.Proof.Coverage
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

private theorem normalized_table (input : State) (i : Nat) :
    (scanState input i).opportunistic = input.opportunistic := by
  unfold scanState
  dsimp only
  split <;> rfl

private theorem commit_zero {ctx : Ctx} {block i : Nat} {input next : State}
    (empty : NoOpportunity input)
    (run : commitOpportunistic ctx block i input = .ok (some next)) :
    ∀ v ∈ ctx.insts[i]!.results, input.demand[v]! = 0 := by
  unfold commitOpportunistic at run
  dsimp only at run
  cases guard : ctx.insts[i]!.results.all (fun v => input.demand[v]! == 0 ||
      input.opportunistic[v]!.any (fun o => o.block == block && o.count == input.demand[v]!)) with
  | false => simp only [guard, Bool.not_false, ite_true] at run; cases run
  | true =>
    intro v member
    have used := List.all_eq_true.mp guard v member
    rw [empty v] at used
    simpa only [Option.any_none, Bool.or_false, beq_iff_eq] using used

/-- An actual scan entered with an empty remembered table cannot choose the
opportunistic path: zero demands would already choose omission. -/
theorem scan_noOpportunistic {ctx : Ctx} {block i ti : Nat} {isBranch : Bool}
    {input : State} {output : Scan} {step : Step} (empty : NoOpportunity input)
    (run : scanInstruction ctx block i ti isBranch input = .ok output)
    (recorded : output.step = some step) : step.decision ≠ .opportunistic := by
  intro decision
  have beforeEmpty : NoOpportunity (scanState input i) := by
    intro v
    rw [normalized_table]
    exact empty v
  have rejectEmission (h : (emitInstruction ctx i (scanState input i) >>= fun e =>
      pure (e.scan block i (scanState input i))) = .ok output) : False := by
    cases emitted : emitInstruction ctx i (scanState input i) with
    | error e => simp only [emitted, bind, Except.bind] at h; cases h
    | ok emission =>
      simp only [emitted, bind, Except.bind, pure, Except.pure] at h
      cases h; cases recorded; cases decision
  unfold scanInstruction at run
  dsimp only at run
  generalize mandatoryEq : (if i == ti then true else ctx.insts[i]!.clif.any mustLower) = mandatory at run
  split at run
  · cases run; cases recorded; cases decision
  · split at run
    · cases run; cases recorded
    · split at run
      · cases run; cases recorded; cases decision
      · rename_i notOmitted
        split at run
        · rename_i committing
          cases call : commitOpportunistic ctx block i (scanState input i) with
          | error e => simp only [call, bind, Except.bind] at run; cases run
          | ok result =>
            simp only [call, bind, Except.bind] at run
            cases result with
            | none => exact rejectEmission run
            | some next =>
              have zero := commit_zero beforeEmpty call
              have noDemand : ctx.insts[i]!.results.any
                  (fun v => (scanState input i).demand[v]! != 0) = false := by
                apply List.any_eq_false.mpr
                intro v member
                simp only [zero v member, bne_self_eq_false, Bool.false_eq_true, not_false_eq_true]
              have mandatoryFalse : mandatory = false := by
                have both := committing
                simp only [Bool.and_eq_true, Bool.not_eq_true'] at both
                exact both.2
              exact notOmitted (by simp only [mandatoryFalse, noDemand, Bool.not_false, Bool.true_and])
        · exact rejectEmission run

private theorem scans_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec exec indices input output) :
    ∀ record ∈ output.records, exec record.inst record.input = .ok record.output := by
  induction cert with
  | nil input => simp
  | cons head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member

private theorem record_execute {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {record : ScanRecord}
    (records : record ∈ event.output.records) :
    scanInstruction event.ctx event.block record.inst event.termInst event.isBranch record.input =
      .ok record.output := by
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, bi, data, core, build, ordered, initial, empty, parts, folded,
    final, prefixRun, nodeRun, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  rw [eventEq] at records ⊢
  have actual := (stock_lowerBlockCore_scanOrigin coreRun).2.2.2.2.2
  exact scans_execute (runScans_spec actual) record records

/-- An actual retained whole-driver source record cannot select remembered
opportunistic binding. Its empty input and real transition are derived. -/
theorem lower_record_noOpportunistic {f : Clif.Function} (scope : LowerScope f) {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {record : ScanRecord}
    (records : record ∈ event.output.records) {step : Step}
    (recorded : record.output.step = some step) : step.decision ≠ .opportunistic := by
  have empty := (lower_records_noOpportunity scope run events).2 record records
  have actual := record_execute run events records
  exact scan_noOpportunistic empty.1 actual recorded

/-- The real emitted call supplies an actual whole-driver record and selection
step, rather than a fabricated or unreachable opportunistic state. -/
theorem lower_record_noOpportunistic_witness :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step),
      LowerScope f ∧ Stock.lower f = .ok result ∧ event ∈ result.blockScans.toList ∧
      record ∈ event.output.records ∧ record.output.step = some step ∧ step.decision = .emitted ∧
      step.decision ≠ .opportunistic := by
  obtain ⟨f, result, event, record, step, scope, run, events, records, recorded, emitted,
    input, before, after⟩ := lower_records_noOpportunity_witness
  exact ⟨f, result, event, record, step, scope, run, events, records, recorded, emitted,
    lower_record_noOpportunistic scope run events records recorded⟩

/-- The same actual source record inhabits the local transition theorem. -/
theorem scan_noOpportunistic_witness :
    ∃ (ctx : Ctx) (block i ti : Nat) (branch : Bool) (input : State) (output : Scan) (step : Step),
      NoOpportunity input ∧ scanInstruction ctx block i ti branch input = .ok output ∧
      output.step = some step ∧ step.decision = .emitted ∧ step.decision ≠ .opportunistic := by
  obtain ⟨f, result, event, record, step, scope, run, events, records, recorded, emitted,
    input, before, after⟩ := lower_records_noOpportunity_witness
  have actual := record_execute run events records
  exact ⟨event.ctx, event.block, record.inst, event.termInst, event.isBranch, record.input,
    record.output, step, before, actual, recorded, emitted, scan_noOpportunistic before actual recorded⟩

end Backend.Stock.Proof.Coverage
