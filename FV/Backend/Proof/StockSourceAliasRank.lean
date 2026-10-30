import FV.Backend.Proof.StockSourceTerminal
import FV.Backend.Proof.StockCoverageRecords

/-! Reuse the existing provenance-count rank for mapped Stock source aliases.
The rank is over source IDs, independent of their allocated register numbers. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

/-- Number of source values reached through the operands of a definition. -/
noncomputable def sourceAliasRank (ctx : Ctx) (x : Nat) : Nat := by
  classical
  exact (List.range ctx.valTy.size).countP fun y =>
    decide (∃ d, ctx.defInst? x = some d ∧ Prov ctx d y)

private theorem provenance_source {ctx original : Ctx}
    (view : DFGViewEq ctx original) {d y : Nat} (reached : Prov ctx d y) :
    Prov original d y := by
  induction reached with
  | arg info originalInst member =>
    exact .arg (by simpa only [view.insts] using info) originalInst member
  | dep _ defined info originalInst member ih =>
    exact .dep ih (by simpa only [Ctx.defInst?, view.valDef] using defined)
      (by simpa only [view.insts] using info) originalInst member

private theorem provenance_not_self {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (dominated : Dominated f)
    {x d : Nat} (definition : ctx.defInst? x = some d) : ¬ Prov ctx d x := by
  intro reached
  obtain ⟨original, before, old, spec, view⟩ := buildCtx_source build
  have defined : original.defInst? x = some d := by
    simpa only [Ctx.defInst?, view.valDef] using definition
  obtain ⟨bi, b, j, stm, block, statement, member, rfl⟩ := (spec.facts.defs dominated.ssa x d).mp defined
  have available := prov_avail dominated old block statement (provenance_source view reached)
  exact ((mem_av block).mp available).2 ⟨j, stm, Nat.le_refl _, statement, member⟩

/-- Actual context construction and the original dominance condition make
provenance strictly decrease this rank whenever the reached value is defined. -/
theorem stock_source_provenance_rank {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (dominated : Dominated f)
    {x y d e : Nat} (definition : ctx.defInst? x = some d)
    (reached : Prov ctx d y) (targetDefinition : ctx.defInst? y = some e) :
    sourceAliasRank ctx y < sourceAliasRank ctx x := by
  classical
  obtain ⟨original, before, old, spec, view⟩ := buildCtx_source build
  have targetOld : original.defInst? y = some e := by
    simpa only [Ctx.defInst?, view.valDef] using targetDefinition
  obtain ⟨bi, b, j, stm, block, statement, member, _⟩ := (spec.facts.defs dominated.ssa y e).mp targetOld
  have bound : y < ctx.valTy.size := by
    rw [view.valTy, spec.facts.size.2.2, ← spec.facts.size.1]
    exact (spec.facts.vals y (mem_valueDefs_res block statement member)).1
  unfold sourceAliasRank
  apply certCountP_lt (a := y)
  · intro z _ included
    simp only [decide_eq_true_eq] at included ⊢
    obtain ⟨k, lookup, prov⟩ := included
    rw [targetDefinition] at lookup
    cases lookup
    exact ⟨d, definition, prov_trans reached targetDefinition prov⟩
  · exact List.mem_range.mpr bound
  · simp only [decide_eq_true_eq]
    exact ⟨d, definition, reached⟩
  · simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro k lookup prov
    rw [targetDefinition] at lookup
    cases lookup
    exact provenance_not_self build dominated targetDefinition prov

private theorem results_definition {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (ssa : (valueDefs f).Nodup)
    {i x : Nat} {info : IInfo} (lookup : ctx.insts[i]? = some info)
    (member : x ∈ info.results) : ctx.defInst? x = some i := by
  obtain ⟨original, before, old, spec, view⟩ := buildCtx_source build
  have oldLookup : original.insts[i]? = some info := by rw [← view.insts]; exact lookup
  have table : info ∈ original.insts.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? oldLookup)
  rcases spec.insts info table with placeholder | ⟨b, blockMember, stm, stmtMember, same⟩
  · rw [placeholder] at member; cases member
  · subst info
    obtain ⟨bi, block⟩ := List.getElem?_of_mem blockMember
    obtain ⟨j, statement⟩ := List.getElem?_of_mem stmtMember
    have defined := defInst_res spec.facts ssa block statement member
    obtain ⟨other, otherLookup, _, otherResults⟩ := spec.facts.stmt bi b j stm block statement
    have sourceLookup : ctx.insts[blockStart f bi + j]? = some other := by
      rw [view.insts]; exact otherLookup
    have equal := stock_buildCtx_result_unique build ssa lookup sourceLookup member
      (by simpa only [otherResults, infoOf] using member)
    rw [← equal] at defined
    simpa only [Ctx.defInst?, view.valDef] using defined

private theorem normalized_frontier (st : State) (i : Nat) :
    (scanState st i).base.nextVreg = st.base.nextVreg := by
  unfold scanState
  dsimp only
  split <;> rfl

/-- A real recorded final source-to-source alias has operand provenance whenever
its target is itself aliased. Fresh and reserved alternatives are excluded by
actual final-array bounds and source/reservation separation. -/
theorem stock_recorded_source_alias_provenance {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (eventMem : event ∈ result.blockScans.toList) (recordMem : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {x key y target next : Nat} {info : IInfo} {inst : Clif.Inst}
    (source : result.ctx.insts[record.inst]? = some info) (original : info.clif = some inst)
    (defines : x ∈ info.results) (mapped : result.ctx.valueReg? x = some (.vreg key .int))
    (targetMapped : result.ctx.valueReg? y = some (.vreg target .int))
    (entry : (result.final.alias[key]?).join = some target)
    (targetEntry : (result.final.alias[target]?).join = some next) : Prov result.ctx record.inst y := by
  rcases stock_lower_emitted_record_finalAliasOrigins_noInherited run scope
      (fun h => scope.nonempty (List.length_eq_zero_iff.mp h)) dominated.ssa
      eventMem recordMem recorded emitted source original defines mapped target entry with
      fresh | ⟨z, reached, register⟩ | reserved
  · have inside : target < result.final.alias.size := by
      apply Nat.lt_of_not_ge
      intro outside
      rw [Array.getElem?_eq_none (by omega : result.final.alias.size ≤ target)] at targetEntry
      cases targetEntry
    have bound := stock_lower_blockScanAliasBounds run event eventMem record recordMem
    rw [normalized_frontier] at bound
    omega
  · obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
        label, bi, data, core, build, _⟩ := stock_lower_blockScanOrigin run eventMem
    have same := (buildCtx_allocated build).2.1 z y target register targetMapped
    subst z
    exact reached
  · exact (reserved.2.2 y targetMapped).elim

/-- Following a recorded source alias to another aliased source strictly
reduces the inherited provenance rank. Target definedness is derived from the
whole-driver terminal theorem, rather than required from the caller. -/
theorem stock_recorded_source_alias_rank {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (eventMem : event ∈ result.blockScans.toList) (recordMem : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {x key y target next : Nat} {info : IInfo} {inst : Clif.Inst}
    (source : result.ctx.insts[record.inst]? = some info) (original : info.clif = some inst)
    (defines : x ∈ info.results) (mapped : result.ctx.valueReg? x = some (.vreg key .int))
    (targetMapped : result.ctx.valueReg? y = some (.vreg target .int))
    (entry : (result.final.alias[key]?).join = some target)
    (targetEntry : (result.final.alias[target]?).join = some next) :
    sourceAliasRank result.ctx y < sourceAliasRank result.ctx x := by
  have reached := stock_recorded_source_alias_provenance run scope dominated eventMem recordMem
    recorded emitted source original defines mapped targetMapped entry targetEntry
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
      label, bi, data, core, build, _⟩ := stock_lower_blockScanOrigin run eventMem
  have definition := results_definition build dominated.ssa source defines
  cases targetDefinition : result.ctx.defInst? y with
  | none =>
    have absent := (stock_lower_undefinedSource_terminal run dominated.ssa targetDefinition targetMapped).1
    rw [absent] at targetEntry
    cases targetEntry
  | some e => exact stock_source_provenance_rank build dominated definition reached targetDefinition

/-- An actual final source alias whose producing scan record is retained.
Both source mappings and the installed final edges are part of the observation. -/
def RecordedSourceAlias (result : Result) (x y : Nat) : Prop :=
  ∃ (event : BlockScanEvent) (record : ScanRecord) (step : Step)
    (info : IInfo) (inst : Clif.Inst) (key target next : Nat),
    event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
    record.output.step = some step ∧ step.decision = .emitted ∧
    result.ctx.insts[record.inst]? = some info ∧ info.clif = some inst ∧
    x ∈ info.results ∧ result.ctx.valueReg? x = some (.vreg key .int) ∧
    result.ctx.valueReg? y = some (.vreg target .int) ∧
    (result.final.alias[key]?).join = some target ∧
    (result.final.alias[target]?).join = some next

/-- A nonempty path of final source aliases observed at their actual records. -/
inductive RecordedSourcePath (result : Result) : Nat → Nat → Prop where
  | single {x y : Nat} (edge : RecordedSourceAlias result x y) : RecordedSourcePath result x y
  | cons {x y z : Nat} (head : RecordedSourceAlias result x y)
      (tail : RecordedSourcePath result y z) : RecordedSourcePath result x z

/-- Any length of actual recorded source-alias chain strictly decreases rank. -/
theorem stock_recorded_source_chain_rank {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {x y : Nat} (path : RecordedSourcePath result x y) :
    sourceAliasRank result.ctx y < sourceAliasRank result.ctx x := by
  have one {a b : Nat} (edge : RecordedSourceAlias result a b) :
      sourceAliasRank result.ctx b < sourceAliasRank result.ctx a := by
    obtain ⟨event, record, step, info, inst, key, target, next, eventMem, recordMem,
      recorded, emitted, source, original, defines, mapped, targetMapped, entry, targetEntry⟩ := edge
    exact stock_recorded_source_alias_rank run scope dominated eventMem recordMem
      recorded emitted source original defines mapped targetMapped entry targetEntry
  induction path with
  | single edge => exact one edge
  | cons head tail ih => exact Nat.lt_trans ih (one head)

/-- Recorded source aliases cannot form a cycle under the original input conditions. -/
theorem stock_recorded_source_chain_noCycle {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (x : Nat) : ¬ RecordedSourcePath result x x := by
  intro path
  exact Nat.lt_irrefl _ (stock_recorded_source_chain_rank run scope dominated path)

private def chainFunction : Clif.Function := {
  name := "recorded_source_chain"
  sig := {returns := [⟨.i8, .none, .normal⟩], callConv := some .systemV}
  blocks := [{id := 0, body := [⟨[0], .iconst .i64 7⟩,
    ⟨[1], .ireduce .i32 0⟩, ⟨[2], .ireduce .i8 1⟩], term := .ret [2]}] }
private def chainBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx chainFunction).toOption.getD (sinkCtx, #[], sinkState)
private theorem chainBuild : Stock.buildCtx chainFunction = .ok chainBuilt := rfl
private theorem chainDominated : Dominated chainFunction := by
  constructor
  · decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [chainFunction] at block
      subst b
      constructor
      · intro j stm statement y member
        rcases j with _ | (_ | (_ | j)) <;> simp at statement
        · subst stm; simp [Backend.Proof.Driver.instArgs] at member
        · subst stm; change y ∈ [0] at member
          simp only [List.mem_singleton] at member; subst y
          change 0 ∈ ((availIn chainFunction ctx).getD 0 [] ++ [0]).filter (fun x => decide (x ∉ [1, 2]))
          simp
        · subst stm; change y ∈ [1] at member
          simp only [List.mem_singleton] at member; subst y
          change 1 ∈ ((availIn chainFunction ctx).getD 0 [] ++ [0, 1]).filter (fun x => decide (x ∉ [2]))
          simp
      · intro y member
        change y ∈ [2] at member
        simp only [List.mem_singleton] at member; subst y
        change 2 ∈ ((availIn chainFunction ctx).getD 0 [] ++ [0, 1, 2]).filter (fun x => decide (x ∉ ([] : List Nat)))
        simp
    | succ bi => simp [chainFunction] at block
  · intro ctx ranges st build tl x available notLocal y member
    cases tl <;> simp [parsOf, chainFunction]

private theorem chainScope : LowerScope chainFunction := lowerScope_of (by decide +kernel)
private def chainInfo1 : IInfo := infoOf chainFunction ⟨[1], .ireduce .i32 0⟩
private def chainInfo2 : IInfo := infoOf chainFunction ⟨[2], .ireduce .i8 1⟩
private theorem chainProvenance : Prov chainBuilt.1 2 1 :=
  .arg (info := chainInfo2) rfl rfl (by decide)

/-- A real built context has both definitions and an inhabited provenance edge;
the lowerer does not equate their source IDs with their allocated registers. -/
theorem stock_source_provenance_rank_witness :
    Stock.buildCtx chainFunction = .ok chainBuilt ∧ Dominated chainFunction ∧
    chainBuilt.1.defInst? 2 = some 2 ∧ Prov chainBuilt.1 2 1 ∧
    chainBuilt.1.defInst? 1 = some 1 ∧
    chainBuilt.1.valueReg? 2 = some (.vreg 194 .int) ∧
    chainBuilt.1.valueReg? 1 = some (.vreg 193 .int) ∧
    sourceAliasRank chainBuilt.1 1 < sourceAliasRank chainBuilt.1 2 := by
  exact ⟨chainBuild, chainDominated, rfl, chainProvenance, rfl, rfl, rfl,
    stock_source_provenance_rank chainBuild chainDominated rfl chainProvenance rfl⟩

private theorem chainObserved : (Stock.lower chainFunction).toOption.map (fun r =>
    ((r.final.alias[194]?).join, (r.final.alias[193]?).join, (r.final.alias[192]?).join,
      ([1, 2] : List Nat).all (fun i => r.blockScans.toList.any (fun event =>
        event.output.records.any (fun record => record.inst == i &&
          record.output.step.any (fun step => step.decision == .emitted)))))) =
    some (some 193, some 192, some 195, true) := by
  decide +kernel

/-- Complete lowering of three source statements installs two source aliases
and a fresh constant alias, with both real reduction records retained. This
inhabits the provenance, one-edge rank and multi-edge/no-cycle results together. -/
theorem stock_recorded_source_chain_witness :
    ∃ (f : Clif.Function) (result : Result),
      LowerScope f ∧ Dominated f ∧ Stock.lower f = .ok result ∧
      (result.final.alias[194]?).join = some 193 ∧
      (result.final.alias[193]?).join = some 192 ∧
      (result.final.alias[192]?).join = some 195 ∧
      RecordedSourceAlias result 2 1 ∧ RecordedSourceAlias result 1 0 ∧
      RecordedSourcePath result 2 0 ∧
      sourceAliasRank result.ctx 1 < sourceAliasRank result.ctx 2 ∧
      sourceAliasRank result.ctx 0 < sourceAliasRank result.ctx 2 ∧
      ¬ RecordedSourcePath result 2 2 := by
  have observed := chainObserved
  cases run : Stock.lower chainFunction with
  | error e => simp only [run, Except.toOption, Option.map_none] at observed; cases observed
  | ok result =>
    simp only [run, Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at observed
    obtain ⟨first, second, fresh, all⟩ := observed
    have records (i : Nat) (member : i ∈ ([1, 2] : List Nat)) :
        ∃ event ∈ result.blockScans.toList, ∃ record ∈ event.output.records,
          record.inst = i ∧ ∃ step, record.output.step = some step ∧ step.decision = .emitted := by
      have recorded := List.all_eq_true.mp all i member
      simpa only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Option.any_eq_true] using recorded
    obtain ⟨event2, eventMem2, record2, recordMem2, which2, step2, recorded2, emitted2⟩ := records 2 (by simp)
    obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
      label, bi, data, core, build, _⟩ := stock_lower_blockScanOrigin run eventMem2
    have context : result.ctx = chainBuilt.1 :=
      congrArg Prod.fst (Except.ok.inj (build.symm.trans chainBuild))
    have edge2 : RecordedSourceAlias result 2 1 := by
      refine ⟨event2, record2, step2, chainInfo2, .ireduce .i8 1, 194, 193, 192,
        eventMem2, recordMem2, recorded2, emitted2, ?_, rfl, by decide, ?_, ?_, first, second⟩
      · rw [which2, context]; rfl
      · rw [context]; rfl
      · rw [context]; rfl
    obtain ⟨event1, eventMem1, record1, recordMem1, which1, step1, recorded1, emitted1⟩ := records 1 (by simp)
    have edge1 : RecordedSourceAlias result 1 0 := by
      refine ⟨event1, record1, step1, chainInfo1, .ireduce .i32 0, 193, 192, 195,
        eventMem1, recordMem1, recorded1, emitted1, ?_, rfl, by decide, ?_, ?_, second, fresh⟩
      · rw [which1, context]; rfl
      · rw [context]; rfl
      · rw [context]; rfl
    have path : RecordedSourcePath result 2 0 := .cons edge2 (.single edge1)
    exact ⟨chainFunction, result, chainScope, chainDominated, run, first, second, fresh, edge2, edge1,
      path, stock_recorded_source_chain_rank run chainScope chainDominated (.single edge2),
      stock_recorded_source_chain_rank run chainScope chainDominated path,
      stock_recorded_source_chain_noCycle run chainScope chainDominated 2⟩

end Backend.Stock.Proof
