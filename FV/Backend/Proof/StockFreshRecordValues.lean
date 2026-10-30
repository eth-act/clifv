import FV.Backend.Proof.StockRecordContext
import FV.Backend.Proof.StockFreshAlias

/-! Whole-run result and availability transfer shared by fresh single-result families. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

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
  unfold scanBlock at actual
  exact scans_execute (runScans_spec actual) record records


private theorem emission_alias {ctx : Ctx} {i : Nat} {info : IInfo} {z a d : Nat}
    {input : State} {emission : Emission}
    (source : ctx.insts[i]? = some info) (results : info.results = [z])
    (mapped : ctx.valueReg? z = some (.vreg a .int))
    (run : emitInstruction ctx i input = .ok emission)
    (output : emission.results = [[.vreg d .int]]) :
    (emission.state.alias[a]?).join = some d := by
  have infoBang : ctx.insts[i]! = info := by simp only [getElem!_def, source]
  unfold emitInstruction at run
  rw [infoBang] at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind, Except.bind, pure, Except.pure] at run
    | split at run
  all_goals
    cases run
    simp only at output
    subst output
    rename_i invoke rootOutput rootRun ignored bindCall bound outputEq lengthGuard binding
    have installed := bindResults_virtual ctx rootOutput.2.1 [(z, a, d)] (by
      intro p member
      have equal := List.mem_singleton.mp member
      subst p
      exact mapped)
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at installed
    rw [results] at binding
    simp only [List.zip_cons_cons, List.zip_nil_left] at binding
    rw [installed] at binding
    cases binding
    rw [aliasStep_get]
    simp only [ite_true]

/-- A single fresh virtual result in an actual retained emitted record resolves
there in the final array. Actual binding and SSA supply the installed final alias;
no rule-family alias certificate is required. -/
theorem stock_lower_record_fresh_result {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {inst : Clif.Inst} {z a d : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some inst)
    (results : info.results = [z]) (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (output : step.results = [[.vreg d .int]]) (fresh : record.input.base.nextVreg ≤ d) :
    (result.final.alias[a]?).join = some d ∧ aliasNum result.final.alias a = d := by
  obtain ⟨context, maps, sources⟩ := stock_lower_record_context run scope events
  obtain ⟨emission, actual, scan⟩ := stock_emitted_scan (record_execute run events records) recorded emitted
  have outputs : emission.results = [[.vreg d .int]] := by
    rw [scan] at recorded
    have same : step = ⟨event.block, record.inst, .emitted, scanState record.input record.inst,
      emission.state, emission.results, emission.rules, emission.code⟩ := Option.some.inj recorded.symm
    rw [same] at output
    exact output
  have entry : (result.final.alias[a]?).join = some d := by
    rw [stock_lower_record_finalAliasEntry run (fun h => scope.nonempty (List.length_eq_zero_iff.mp h))
      ssa events records (x := z) (key := a) (sources _ _ _ source clif)
      (by rw [results]; simp) (by rw [← maps]; exact mapped)]
    rw [scan]
    exact emission_alias source results mapped actual outputs
  exact ⟨entry, stock_lower_freshAlias_resolves run
    (Nat.le_trans (stock_lower_blockScanInitialFrontier run event events record records) fresh) a entry⟩

attribute [local semireducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock
private def exampleFunction : Clif.Function := {
  name := "fresh_add_record"
  sig := { params := [⟨.i64, .none, .normal⟩, ⟨.i64, .none, .normal⟩], returns := [⟨.i64, .none, .normal⟩], callConv := some .systemV }
  blocks := [{ id := 0, params := [(7, .i64), (31, .i64)], body := [⟨[100], .binary .iadd .i64 7 31⟩], term := .ret [100] }] }
private theorem exampleScope : LowerScope exampleFunction := lowerScope_of (by decide +kernel)
private def exampleCode : MInst := .aluRRR .add .size64 (.vreg 195 .int) (.vreg 192 .int) (.vreg 193 .int)
private theorem observed : (Stock.lower exampleFunction).toOption.map (fun result =>
    result.blockScans.toList.any (fun event => event.output.records.any (fun record =>
      record.inst == 0 && record.input.base.nextVreg == 195 &&
      decide ((event.ctx.insts[0]?).map (fun info => (info.clif, info.results)) =
        some (some (.binary .iadd .i64 7 31), [100])) &&
      decide (event.ctx.valueReg? 100 = some (.vreg 194 .int)) &&
      record.output.step.any (fun step => step.decision == .emitted &&
        decide (step.results = [[.vreg 195 .int]])) && decide (record.output.emitted = #[exampleCode])))) = some true := by
  decide +kernel

/-- A complete Stock add lowering run retains the real sparse-ID source record,
whose actual emitter installs194→195 and whose final resolver reaches195. -/
theorem stock_lower_record_fresh_result_witness :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step),
      Stock.lower exampleFunction = .ok result ∧ LowerScope exampleFunction ∧
      (valueDefs exampleFunction).Nodup ∧ event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.inst = 0 ∧ record.output.step = some step ∧ step.decision = .emitted ∧
      step.results = [[.vreg 195 .int]] ∧ record.output.emitted = #[exampleCode] ∧
      (result.final.alias[194]?).join = some 195 ∧ aliasNum result.final.alias 194 = 195 := by
  have actual := observed
  cases run : Stock.lower exampleFunction with
  | error e => simp only [run, Except.toOption, Option.map_none] at actual; cases actual
  | ok result =>
    simp only [run, Except.toOption, Option.map_some, Option.some.injEq] at actual
    obtain ⟨event, events, record, records, current, frontier, sourceData, mapped, stepData, code⟩ :=
      (by simpa only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using actual :
        ∃ event ∈ result.blockScans.toList, ∃ record ∈ event.output.records,
          record.inst = 0 ∧ record.input.base.nextVreg = 195 ∧
          (event.ctx.insts[0]?).map (fun info => (info.clif, info.results)) = some (some (.binary .iadd .i64 7 31), [100]) ∧
          event.ctx.valueReg? 100 = some (.vreg 194 .int) ∧
          record.output.step.any (fun step => step.decision == .emitted && decide (step.results = [[.vreg 195 .int]])) = true ∧
          record.output.emitted = #[exampleCode])
    obtain ⟨info, source, clif, results⟩ := (by
      simpa only [Option.map_eq_some_iff, Prod.mk.injEq] using sourceData :
        ∃ info, event.ctx.insts[0]? = some info ∧ info.clif = some (.binary .iadd .i64 7 31) ∧ info.results = [100])
    obtain ⟨step, recorded, emitted, outputs⟩ := (by
      simpa only [Option.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using stepData :
        ∃ step, record.output.step = some step ∧ step.decision = .emitted ∧ step.results = [[.vreg 195 .int]])
    have ssa : (valueDefs exampleFunction).Nodup := by decide +kernel
    have final := stock_lower_record_fresh_result run exampleScope ssa events records
      (by simpa only [current] using source) clif results mapped recorded emitted outputs (by rw [frontier]; exact Nat.le_refl _)
    exact ⟨result, event, record, step, rfl, exampleScope, ssa, events, records, current, recorded, emitted, outputs, code, final⟩

end Backend.Stock.Proof
