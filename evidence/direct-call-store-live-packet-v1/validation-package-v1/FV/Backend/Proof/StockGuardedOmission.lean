import FV.Backend.Proof.StockSelectScanRefines

/-! Actual omitted records preserve the same indexed, source-availability-guarded
relation as emitted pure families. This includes real successful nontrapping
loads, without requiring their ignored results to have machine registers. -/
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

private theorem statement_results {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord} (events : event ∈ result.blockScans.toList)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {inst : Clif.Inst}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some inst) :
    info.results = stm.results := by
  have globalSource := (stock_lower_record_context run scope events).2.2 _ _ _ source clif
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, nodeBi, data, core, build, ordered, initial, empty, parts, folded,
    final, prefixRun, nodeRun, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original, st0, oldBuild, spec, view⟩ := buildCtx_source build
  obtain ⟨other, found, originalClif, results⟩ := spec.facts.stmt bi b j stm block statement
  have actual : original.insts[blockStart f bi + j]? = some info := by
    rw [← view.insts, ← current]; exact globalSource
  cases Option.some.inj (found.symm.trans actual)
  exact results

/-- Every actual omitted ordinary source record discharges the guarded indexed
scan obligation. The original driver run derives its scan execution, zero demand
for ignored results, and empty code; original SSA derives post-source DFG. -/
theorem stock_lower_omitted_scan_fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {step : Step} (recorded : record.output.step = some step) (omitted : step.decision = .omitted)
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx bi) isem result.final.alias
      (GuardedScanRel f result event.ctx bi MR) record := by
  intro s s' hsource ρ w held
  obtain ⟨indexed, advance, sourceStep⟩ := hsource
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func, dfg, memory, values⟩ := held
  rw [position] at dfg values
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨info,inst,vals,regs,rest,source,clif,body,outcome,set,updated⟩ := sourceStep
  have executed := record_execute run events records
  have facts := scan_omitted_semantic (env := env) (p := cp) (cm := s.2.2) (ρ := fun k => ρ (aliasNum result.final.alias k))
    executed recorded omitted source clif set
  have unchanged := facts.2.1 _ _ outcome
  have resultNames := statement_results run scope events block statement current source clif
  have bang : event.ctx.insts[record.inst]! = info := by simp only [getElem!_def,source]
  have zeros : ∀ x ∈ info.results, record.input.demand[x]! = 0 := by
    simpa only [bang] using (scan_omitted executed recorded omitted).2.2.1
  refine ⟨ρ,w,?_,?_,?_,?_,?_⟩
  · simp only [facts.2.2.2.2, Array.toList_empty,List.map_nil,seqRun]
  · rw [updated]; exact func
  · simpa only [advance,position] using postDFG
  · rw [updated,unchanged]; exact memory
  · intro x required v lookup
    have notResult : x ∉ info.results := fun member => required.1 (zeros x member)
    have before := available_before_of_after_not_result block statement
      (by simpa only [advance,position] using required.2) (by rwa [← resultNames])
    have demanded : Demanded record.output.state x := by
      simpa only [facts.1,Demanded,scanState_demands] using required.1
    have old : s.2.1.regs x = some v := by
      rw [updated] at lookup
      change regs x = some v at lookup
      rwa [setMany_other set notResult] at lookup
    exact values x ⟨demanded,before⟩ v old
end Backend.Stock.Proof
