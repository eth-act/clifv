import FV.Backend.Proof.IselGeneric
import FV.Backend.Proof.StockFreshRecordValues

/-! Actual selected-rule receipts from Stock named roots and retained records. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

/-- The actual first matching rule, its rejected prefix, match/RHS executions
and final fired trace. No choice of rule is supplied by the caller. -/
structure LowerSelection (ctx : Ctx) (i : Nat) (before : State)
    (out : V) (next : State) (trace : List RuleId) where
  rule : Rule
  pre : List Rule
  post : List Rule
  candidates : program.rulesOf T.lower.id = pre ++ rule :: post
  rejected : ∀ r ∈ pre, ∃ m, 999999 ≤ m + 2 + (program.rulesOf T.lower.id).length ∧
    ∃ after, (matchRule program (Stock.sem ctx) {} m r [.inst i]).run (before, #[]) = .ok (none, after)
  matchFuel : Nat
  env : Isle.Interp.Env V
  matched : State
  matchTrace : Array RuleId
  rhsTrace : Array RuleId
  fuelBound : 999999 ≤ matchFuel + 2 + (program.rulesOf T.lower.id).length
  matchedRun : (matchRule program (Stock.sem ctx) {} matchFuel rule [.inst i]).run (before, #[]) =
    .ok (some env, matched, matchTrace)
  rhsRun : (evalExpr program (Stock.sem ctx) {} 999999 rule.rhs env).run (matched, matchTrace) =
    .ok (some out, next, rhsTrace)
  fired : trace = (rhsTrace.push rule.id).toList

/-- A successful actual named lower call supplies complete first-match
selection receipts through the existing generic interpreter inversion. -/
theorem stock_named_lower_selection {ctx : Ctx} {i : Nat} {before next : State} {out : V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower" [.inst i] before = .ok (some out, next, trace)) :
    Nonempty (LowerSelection ctx i before out next trace) := by
  unfold Stock.runTerm Interp.run at run
  rw [program_termByName_lower] at run
  dsimp only at run
  cases call : (applyTerm program (Stock.sem ctx) {} 1000000 T.lower.ret T.lower.id [.inst i]).run
      (before, #[]) with
  | error e => rw [call] at run; cases run
  | ok q =>
    obtain ⟨v, after, fired⟩ := q
    rw [call] at run
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl, rfl⟩ := run
    obtain ⟨r, pre, post, candidates, rejected, fuel, env, middle, final, rhsTrace,
      fuelBound, matchedRun, rhsRun, stateEq⟩ :=
      applyTerm_internal_some_first (p := program) (sem := Stock.sem ctx) (cfg := {}) rfl
        data_program.t686 rfl rfl (n := 999999) call
    have finalEq := congrArg Prod.fst stateEq
    have traceEq := congrArg Prod.snd stateEq
    change after = final at finalEq
    subst final
    exact ⟨⟨r, pre, post, candidates, rejected, fuel, env, middle.1, middle.2, rhsTrace,
      fuelBound, matchedRun, rhsRun, congrArg Array.toList traceEq⟩⟩

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
    scanInstruction event.ctx event.block record.inst event.termInst event.isBranch record.input = .ok record.output := by
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, bi, data, core, build, ordered, initial, empty, parts, folded,
    final, prefixRun, nodeRun, suffixRun, node, coreRun, eventEq, stateEq⟩ := stock_lower_blockScanOrigin run events
  rw [eventEq] at records ⊢
  have actual := (stock_lowerBlockCore_scanOrigin coreRun).2.2.2.2.2
  unfold scanBlock at actual
  exact scans_execute (runScans_spec actual) record records

/-- Every actual retained emitted record exposes its real named call, selected
rule, output conversion and binding, including extra physical-result copies. -/
structure RecordSelection (event : BlockScanEvent) (record : ScanRecord) (step : Step) where
  out : V
  next : State
  bound : State
  fired : List RuleId
  results : List (List Reg)
  copies : Array MInst
  rootRun : Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
    .ok (some out, next, fired)
  selected : LowerSelection event.ctx record.inst (scanState record.input record.inst) out next fired
  output : out = .regsVec results
  binding : bindResults event.ctx (event.ctx.insts[record.inst]!.results.zip results) next = .ok (bound, copies)
  state : record.output.state = bound
  code : record.output.emitted = bound.base.emitted ++ copies
  resultRegs : step.results = results
  rules : step.rules = fired

/-- Whole-driver execution supplies selection and binding receipts for every
actual emitted record; no caller match/RHS/root certificate is required. -/
theorem stock_lower_record_selection {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    Nonempty (RecordSelection event record step) := by
  obtain ⟨emission, call, scan⟩ := stock_emitted_scan (record_execute run events records) recorded emitted
  unfold emitInstruction at call
  cases root : Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) with
  | error e => simp only [root, bind, Except.bind] at call; cases call
  | ok result =>
    obtain ⟨out, next, fired⟩ := result
    simp only [root, bind, Except.bind] at call
    cases out with
    | none => cases call
    | some out =>
      cases out <;> try (cases call)
      rename_i rss
      dsimp only at call
      split at call
      · cases call
      · cases binding : bindResults event.ctx (event.ctx.insts[record.inst]!.results.zip rss) next with
        | error e => simp only [binding] at call; cases call
        | ok pair =>
          obtain ⟨bound, copies⟩ := pair
          simp only [binding, pure, Except.pure] at call
          cases call
          obtain ⟨selection⟩ := stock_named_lower_selection root
          rw [scan] at recorded
          have stepEq := Option.some.inj recorded.symm
          refine ⟨⟨.regsVec rss, next, bound, fired, rss, copies, root, selection, rfl, binding, ?_, ?_, ?_, ?_⟩⟩
          · rw [scan]; rfl
          · rw [scan]; rfl
          · rw [stepEq]
          · rw [stepEq]

/-- The selected rule is an actual candidate of the production lower term. -/
theorem LowerSelection.rule_mem {ctx : Ctx} {i : Nat} {before next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i before out next trace) : selected.rule ∈ program.rulesOf T.lower.id := by
  rw [selected.candidates]
  simp

/-- The final fired ID identifies the actual root rule rather than a nested helper. -/
theorem LowerSelection.last_rule {ctx : Ctx} {i : Nat} {before next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i before out next trace) : trace.getLast? = some selected.rule.id := by
  have traceEq := congrArg List.getLast? selected.fired
  exact traceEq.trans (by simp only [Array.toList_push]; simp)

/-- A complete sparse-ID add lowering supplies an actual emitted record and
inhabits both named-root and whole-record selection receipts, membership and trace. -/
theorem stock_lower_record_selection_witness :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step),
      Stock.lower f = .ok result ∧ event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧ Nonempty (RecordSelection event record step) ∧
      ∃ (out : V) (next : State) (fired : List RuleId) (selection : LowerSelection event.ctx record.inst
          (scanState record.input record.inst) out next fired),
        Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
          .ok (some out, next, fired) ∧ selection.rule ∈ program.rulesOf T.lower.id ∧
          fired.getLast? = some selection.rule.id := by
  obtain ⟨result, event, record, step, run, scope, ssa, events, records, current, recorded, emitted, _, _, _⟩ :=
    stock_lower_record_fresh_result_witness
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  exact ⟨_, result, event, record, step, run, events, records, recorded, emitted, ⟨receipt⟩,
    receipt.out, receipt.next, receipt.fired, receipt.selected, receipt.rootRun,
    receipt.selected.rule_mem, receipt.selected.last_rule⟩

end Backend.Stock.Proof
