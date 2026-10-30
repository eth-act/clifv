import FV.Backend.Proof.StockRecordContext
import FV.Backend.Proof.StockAvailableValues
import FV.Backend.Proof.StockRecordIntervals
import FV.Backend.Proof.StockRecordFinalAlias
import FV.Backend.Proof.StockEmittedScan

/-! Constant value transfer for records retained by an actual whole-driver run.
Final alias resolution and other-value noninterference are derived from that run. -/
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

private theorem scan_next (st : State) (i : Nat) :
    (scanState st i).base.nextVreg = st.base.nextVreg := by
  unfold scanState
  dsimp only
  split <;> rfl
private theorem scan_empty (st : State) (i : Nat) :
    (scanState st i).base.emitted = #[] := by
  unfold scanState
  dsimp only
  split <;> rfl

/-- Selected constant code in an actual retained record establishes its source
result and preserves all other demanded source-available values. The whole run
supplies final alias resolution, allocation boundedness and noninterference. -/
theorem stock_lower_constant_available_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {inst : Clif.Inst} {x a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some inst)
    (results : stm.results = [x]) (infoResults : info.results = [x])
    (mapped : event.ctx.valueReg? x = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (semantics : ∀ aliases i, isem (i.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size + 1))) = isem i)
    {m n : Nat} (matchFuel : 2 ≤ m) (evalFuel : 50 ≤ n)
    {matched next : State} {matchTrace evalTrace : Array RuleId}
    {env : Isle.Interp.Env V} {out : V} {trace : List RuleId}
    (matchRun : (matchRule program (Stock.sem event.ctx) {} m rule_lower_53 [.inst record.inst]).run
      (scanState record.input record.inst, #[]) = .ok (some env, matched, matchTrace))
    (evalRun : (evalExpr program (Stock.sem event.ctx) {} n rule_lower_53.rhs env).run
      (matched, matchTrace) = .ok (some out, next, evalTrace))
    (rootRun : Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
      .ok (some out, next, trace)) :
    ∃ (ty : Clif.Ty) (imm : BitVec ty.width) (d : Nat),
      inst = .iconst ty imm ∧ aliasNum result.final.alias a = d ∧
      record.output.state.demand = record.input.demand ∧
      ∀ (fr : Clif.Frame) (ρ : Nat → CV),
        ValuesHeld (fun y => Demanded record.output.state y ∧
          y ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr
            (fun k => ρ (aliasNum result.final.alias k)) →
        ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
          VHolds ⟨ty, imm⟩ (ρ' d) ∧
          ValuesHeld (fun y => Demanded record.input y ∧
            y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
              (withValue fr x ⟨ty, imm⟩) (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨context, maps, sources⟩ := stock_lower_record_context run scope events
  obtain ⟨ty, imm, ms, d, bound, constant, output, binding, boundEq, shape, execution⟩ :=
    stock_iconst_available_resolved data_program context source clif rfl refines semantics
      matchFuel evalFuel matchRun evalRun block statement results infoResults mapped
  have evalRun' := evalRun
  have rootRun' := rootRun
  rw [output] at evalRun' rootRun'
  obtain ⟨selected, selectedRun, selectedState, selectedCode, selectedResults⟩ :=
    stock_iconst_emission_alias data_program source infoResults mapped rfl matchRun evalRun' rootRun'
  obtain ⟨actual, actualRun, actualScan⟩ := stock_emitted_scan
    (record_execute run events records) recorded emitted
  have same : selected = actual := Except.ok.inj (selectedRun.symm.trans actualRun)
  rw [← same] at actualScan
  have full : next = {scanState record.input record.inst with base := next.base} := by
    rw [stock_iconst_rhs_frame data_program event.ctx rfl evalRun,
      stock_iconst_match_frame data_program event.ctx rfl matchRun]
  have boundState : bound = selected.state := by
    rw [boundEq, full, selectedState]
  have code : record.output.emitted.toList = ms := by
    rw [actualScan]
    change selected.code.toList = ms
    rw [selectedCode]
    have boundBase : bound.base = next.base := by rw [boundEq]
    rw [← boundBase, shape.emitted, scan_empty, Array.empty_append, List.toList_toArray]
  have demands : record.output.state.demand = record.input.demand := by
    rw [actualScan]
    change selected.state.demand = record.input.demand
    rw [selectedState]
    exact scanState_demands _ _
  have aliasesBound := stock_lower_blockScanAliasBounds run event events record records
  have entry : (result.final.alias[a]?).join = some d := by
    rw [stock_lower_record_finalAliasEntry run ((fun h => scope.nonempty (List.length_eq_zero_iff.mp h)))
      dominated.ssa events records (x := x) (key := a) (sources _ _ _ source clif)
        (by rw [infoResults]; simp) (by rw [← maps]; exact mapped)]
    rw [actualScan]
    change (selected.state.alias[a]?).join = some d
    rw [selectedState, aliasStep_get]
    simp only [ite_true]
  have target : aliasNum result.final.alias d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none (by have := shape.res; omega)]
    rfl
  have resolved : aliasNum result.final.alias a = d :=
    (stock_lower_alias_step run scope dominated entry).trans target
  refine ⟨ty, imm, d, constant, resolved, demands, ?_⟩
  intro fr ρ held
  obtain ⟨ρ', executed, value, installed⟩ := execution result.final.alias aliasesBound ρ
  have heldBefore : ValuesHeld (fun y => Demanded record.input y ∧
      y ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr
        (fun k => ρ (aliasNum result.final.alias k)) := by
    simpa only [ValuesHeld, Demanded, demands] using held
  have heldAfter := installed (Demanded record.input) fr heldBefore resolved (by
    intro y key _ available map _
    have excluded := stock_lower_available_alias_outside_record run scope dominated events records
      block statement current available (by rw [← maps]; exact map)
    rw [scan_next, boundState] at *
    simpa only [actualScan, Emission.scan] using excluded)
  exact ⟨ρ', by simpa only [code] using executed, value, heldAfter⟩

/-- The same actual record refines the source constant instruction step,
including the updated frame and an arbitrary preserved source/machine memory relation. -/
theorem stock_lower_constant_available_source {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {inst : Clif.Inst} {x a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some inst)
    (results : stm.results = [x]) (infoResults : info.results = [x])
    (mapped : event.ctx.valueReg? x = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (semantics : ∀ aliases i, isem (i.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size + 1))) = isem i)
    {m n : Nat} (matchFuel : 2 ≤ m) (evalFuel : 50 ≤ n)
    {matched next : State} {matchTrace evalTrace : Array RuleId}
    {env : Isle.Interp.Env V} {out : V} {trace : List RuleId}
    (matchRun : (matchRule program (Stock.sem event.ctx) {} m rule_lower_53 [.inst record.inst]).run
      (scanState record.input record.inst, #[]) = .ok (some env, matched, matchTrace))
    (evalRun : (evalExpr program (Stock.sem event.ctx) {} n rule_lower_53.rhs env).run
      (matched, matchTrace) = .ok (some out, next, evalTrace))
    (rootRun : Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
      .ok (some out, next, trace)) :
    ∃ (ty : Clif.Ty) (imm : BitVec ty.width), inst = .iconst ty imm ∧
      ∀ (clifEnv : Clif.Env) (cp : Clif.Program) (MR : Clif.Mem → Arm.ArmState → Prop),
        (∀ cm w w', SameWorld F w' w → MR cm w → MR cm w') →
        ∀ (fr fr' : Clif.Frame) (cm cm' : Clif.Mem) (ρ : Nat → CV) (w : Arm.ArmState),
          SourceInstResult clifEnv cp event.ctx record.inst (fr, cm) (fr', cm') →
          MR cm w →
          ValuesHeld (fun y => Demanded record.output.state y ∧
            y ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr
              (fun k => ρ (aliasNum result.final.alias k)) →
          ∃ ρ' w', seqRun isem (record.output.emitted.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ w =
              some (.fall ρ' w') ∧ MR cm' w' ∧
            ValuesHeld (fun y => Demanded record.input y ∧
              y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx fr'
                (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨ty, imm, d, constant, _, _, transfer⟩ :=
    stock_lower_constant_available_values run scope dominated events records block statement current
      source clif results infoResults mapped recorded emitted refines semantics
      matchFuel evalFuel matchRun evalRun rootRun
  refine ⟨ty, imm, constant, ?_⟩
  intro clifEnv cp MR preserve fr fr' cm cm' ρ w step memory held
  obtain ⟨info', inst', vals, regs, rest, lookup, original, _, evaluated, written, frame⟩ := step
  have sameInfo : info' = info := Option.some.inj (lookup.symm.trans source)
  subst info'
  have sameInst : inst' = inst := Option.some.inj (original.symm.trans clif)
  subst inst'
  rw [constant] at evaluated
  simp only [instOutcome, Clif.evalInst, pure] at evaluated
  obtain ⟨values, sameMem⟩ := Prod.mk.inj (Clif.Res.ok.inj evaluated)
  rw [← values, infoResults] at written
  simp only [Clif.Regs.setMany_cons, Clif.Regs.setMany_nil, Option.some.injEq] at written
  subst regs
  obtain ⟨ρ', executed, _, installed⟩ := transfer fr ρ held
  obtain ⟨w', runCode, world⟩ := executed w
  refine ⟨ρ', w', runCode, ?_, ?_⟩
  · rw [← sameMem]
    exact preserve _ _ _ world memory
  · change fr' = _ at frame
    rw [frame]
    change ValuesHeld (fun y => Demanded record.input y ∧
      y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx (withValue fr x ⟨ty, imm⟩)
        (fun k => ρ' (aliasNum result.final.alias k))
    exact installed

attribute [local semireducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

private def exampleFunction : Clif.Function := {
  name := "constant_record_values"
  sig := { params := [⟨.i64, .none, .normal⟩], returns := [⟨.i64, .none, .normal⟩, ⟨.i8, .none, .normal⟩], callConv := some .systemV }
  blocks := [{id := 0, params := [(7, .i64)], body := [⟨[2], .iconst .i8 9⟩], term := .ret [7, 2]}] }
private theorem exampleScope : LowerScope exampleFunction := lowerScope_of (by decide +kernel)
private theorem exampleDominated : Dominated exampleFunction := by
  constructor
  · decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [exampleFunction] at block
      subst b
      constructor
      · intro j stm statement y member
        cases j <;> simp at statement
        subst stm
        simp [Backend.Proof.Driver.instArgs] at member
      · intro y member
        change y ∈ [7, 2] at member
        change y ∈ (([7] ++ (availIn exampleFunction ctx).getD 0 [] ++ [2]).filter
          (fun x => decide (x ∉ ([] : List Nat))))
        simp only [List.mem_filter, decide_eq_true_eq, List.not_mem_nil, not_false_eq_true, and_true]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp
    | succ bi => simp [exampleFunction] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bounds := (inFix_fixOk (f := exampleFunction) (ctx := ctx) (gn := id)).cand tl x available
    have length : exampleFunction.blocks.length = 1 := rfl
    omega
private def exampleFrame : Clif.Frame := {
  func := exampleFunction
  regs := fun x => if x = 2 then some (.ofInt .i8 77)
    else if x = 7 then some (.ofInt .i64 11) else none
  slots := [], body := [⟨[2], .iconst .i8 9⟩], term := .ret [7, 2] }
private def exampleRegs (n : Nat) : CV := if n = 192 then 11 else 0
private theorem exampleAvailable (ctx : Ctx) :
    ∀ y, y ∈ availOf exampleFunction (availIn exampleFunction ctx) 0 0 ↔ y = 7 := by
  intro y
  have entryEmpty : y ∉ (availIn exampleFunction ctx).getD 0 [] := by
    intro member
    have bounded := (inFix_fixOk (f := exampleFunction) (ctx := ctx) (gn := id)).cand 0 y member
    omega
  rw [mem_av (show exampleFunction.blocks[0]? = some
    ({id := 0, params := [(7, .i64)], body := [⟨[2], .iconst .i8 9⟩], term := .ret [7, 2]} : Clif.Block) from rfl)]
  constructor
  · intro required
    rcases required.1 with param | entry | ⟨k, stm, earlier, _, _⟩
    · exact List.mem_singleton.mp param
    · exact False.elim (entryEmpty entry)
    · omega
  · intro equal
    subst y
    refine ⟨Or.inl (by simp), ?_⟩
    intro ⟨k, stm, _, statement, member⟩
    cases k <;> simp at statement
    subst stm
    simp at member

private theorem exampleObserved : (Stock.lower exampleFunction).toOption.map (fun result =>
    (aliasNum result.final.alias 192, aliasNum result.final.alias 193,
      result.blockScans.toList.any (fun event => event.output.records.any (fun record =>
        record.inst == 0 && record.input.base.nextVreg == 194 &&
        record.input.demand[2]! != 0 &&
        record.output.step.any (fun step => step.decision == .emitted) &&
        decide ((event.ctx.insts[0]?).map (fun info => (info.clif, info.results)) =
          some (some (.iconst .i8 9), [2])) &&
        decide (event.ctx.valueReg? 7 = some (.vreg 192 .int)) &&
        decide (event.ctx.valueReg? 2 = some (.vreg 193 .int)))))) = some (192, 194, true) := by
  decide +kernel

/-- Complete lowering retains the selected source record. Its real named root
executes, stale source77 becomes9, and the demanded parameter stays11. -/
theorem stock_lower_constant_available_values_witness :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (ρ' : Nat → CV),
      Stock.lower exampleFunction = .ok result ∧ LowerScope exampleFunction ∧ Dominated exampleFunction ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      MappedCtxInv exampleFunction event.ctx ∧ record.inst = 0 ∧
      exampleFrame.regs 2 = some (.ofInt .i8 77) ∧
      ¬ VHolds (.ofInt .i8 77) (exampleRegs (aliasNum result.final.alias 193)) ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) exampleRegs ρ' ∧
      VHolds (.ofInt .i8 9) (ρ' 194) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf exampleFunction (availIn exampleFunction result.ctx) 0 1) event.ctx
          (withValue exampleFrame 2 (.ofInt .i8 9)) (fun k => ρ' (aliasNum result.final.alias k)) ∧
      ∃ (fr' : Clif.Frame) (w' : Arm.ArmState),
        SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
          (exampleFrame, Clif.Mem.empty) (fr', Clif.Mem.empty) ∧
        seqRun ispec (record.output.emitted.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1))))
            exampleRegs Arm.ArmState.default = some (.fall ρ' w') ∧
        ValuesHeld (fun y => Demanded record.input y ∧
          y ∈ availOf exampleFunction (availIn exampleFunction result.ctx) 0 1) event.ctx fr'
            (fun k => ρ' (aliasNum result.final.alias k)) := by
  have observed := exampleObserved
  cases run : Stock.lower exampleFunction with
  | error e => simp only [run, Except.toOption, Option.map_none] at observed; cases observed
  | ok result =>
    simp only [run, Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at observed
    obtain ⟨parameterResolved, resultResolved, found⟩ := observed
    obtain ⟨event, events, record, records, current, frontier, demanded, selected, infoData, parameterMap, resultMap⟩ :=
      (by simpa only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq, and_assoc] using found :
        ∃ event ∈ result.blockScans.toList, ∃ record ∈ event.output.records,
          record.inst = 0 ∧ record.input.base.nextVreg = 194 ∧ record.input.demand[2]! ≠ 0 ∧
          record.output.step.any (fun step => step.decision == .emitted) = true ∧
          (event.ctx.insts[0]?).map (fun info => (info.clif, info.results)) = some (some (.iconst .i8 9), [2]) ∧
          event.ctx.valueReg? 7 = some (.vreg 192 .int) ∧ event.ctx.valueReg? 2 = some (.vreg 193 .int))
    obtain ⟨step, recorded, emitted⟩ := (by simpa only [Option.any_eq_true, beq_iff_eq] using selected :
      ∃ step, record.output.step = some step ∧ step.decision = .emitted)
    obtain ⟨info, source, clif, results⟩ := (by
      simpa only [Option.map_eq_some_iff, Prod.mk.injEq] using infoData :
        ∃ info, event.ctx.insts[0]? = some info ∧ info.clif = some (.iconst .i8 9) ∧ info.results = [2])
    have context := (stock_lower_record_context run exampleScope events).1
    have data : ∀ st : LState, Backend.externExtract event.ctx T.inst_data_value (.inst 0) st =
        .ok [.ty (.int 8), .data 152 35 [.data 151 57 [], .int 9]] := by
      intro st
      rw [ext_inst_data_value event.ctx st source]
      have raw := context.data 0 info (.iconst .i8 9) source clif
      change Except.ok (.data 152 35 [.data 151 57 [], .int 9] : V) = .ok info.data at raw
      have dataEq := Except.ok.inj raw
      obtain ⟨tys, types, resTys, _⟩ := context.resTys 0 info (.iconst .i8 9) source clif
      change some [Clif.Ty.i8] = some tys at types
      cases types
      rw [← dataEq, resTys]
      rfl
    obtain ⟨next, trace, root, evaluated, matched⟩ :=
      stock_statement_selectedConstant_context_receipts event.ctx data (scanState record.input 0)
    have refines : Refines (fun _ => True) ispec :=
      fun _ _ _ _ w' _ h => ⟨w', h, SameWorld.refl _ _⟩
    have semantics : ∀ aliases i, ispec (i.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size + 1))) = ispec i := by
      intro aliases i
      funext us w
      have renamed : VRenaming (Backend.lowerFunction.resolve aliases (aliases.size + 1)) (aliasNum aliases) := by
        refine ⟨fun n c => resolve_vreg aliases _ n c, ?_⟩
        intro r hr
        cases r with
        | vreg n c => exact False.elim (hr n c rfl)
        | _ => simp [Backend.lowerFunction.resolve]
      exact ispec_mapRegs renamed us w i
    obtain ⟨tySource, immSource, sourceConstant, transferSource⟩ :=
      stock_lower_constant_available_source run exampleScope exampleDominated events records
        (bi := 0) (j := 0) (b := exampleFunction.blocks[0]!)
        (stm := ⟨[2], .iconst .i8 9⟩) rfl rfl (by simpa only [blockStart, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add] using current)
        (by simpa only [current] using source) clif rfl results resultMap recorded emitted
        refines semantics (m := 999825) (n := 999999) (by decide) (by decide)
        (by simpa only [current] using matched) (by simpa only [current] using evaluated)
        (by simpa only [current] using root)
    obtain ⟨ty, imm, d, constant, resolved, _, execute⟩ :=
      stock_lower_constant_available_values run exampleScope exampleDominated events records
        (bi := 0) (j := 0) (b := exampleFunction.blocks[0]!)
        (stm := ⟨[2], .iconst .i8 9⟩) rfl rfl (by simpa only [blockStart, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add] using current)
        (by simpa only [current] using source) clif rfl results resultMap recorded emitted
        refines semantics (m := 999825) (n := 999999) (by decide) (by decide)
        (by simpa only [current] using matched) (by simpa only [current] using evaluated)
        (by simpa only [current] using root)
    cases sourceConstant
    cases constant
    have resultNumber : d = 194 := resolved.symm.trans resultResolved
    subst d
    have held : ValuesHeld (fun y => Demanded record.output.state y ∧
        y ∈ availOf exampleFunction (availIn exampleFunction result.ctx) 0 0) event.ctx exampleFrame
          (fun k => exampleRegs (aliasNum result.final.alias k)) := by
      intro y required val lookup
      have equal := (exampleAvailable result.ctx y).mp required.2
      subst y
      change some (Clif.Val.ofInt .i64 11) = some val at lookup
      cases lookup
      refine ⟨192, parameterMap, ?_⟩
      change VHolds (.ofInt .i64 11) (exampleRegs (aliasNum result.final.alias 192))
      rw [parameterResolved]
      unfold VHolds exampleRegs
      decide +kernel
    obtain ⟨ρ', executed, value, heldAfter⟩ := execute exampleFrame exampleRegs held
    let fr' : Clif.Frame := {exampleFrame with regs := exampleFrame.regs.set 2 (.ofInt .i8 9), body := []}
    have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (exampleFrame, Clif.Mem.empty) (fr', Clif.Mem.empty) :=
      ⟨info, .iconst .i8 9, [.ofInt .i8 9], exampleFrame.regs.set 2 (.ofInt .i8 9), [],
        by simpa only [current] using source, clif, by rw [results]; rfl,
        rfl, by rw [results]; rfl, rfl⟩
    obtain ⟨ρSource, w', machineStep, _, sourceHeld⟩ := transferSource Clif.Env.empty {funcs := []}
      (fun _ _ => True) (fun _ _ _ _ _ => trivial) exampleFrame fr' Clif.Mem.empty Clif.Mem.empty
      exampleRegs Arm.ArmState.default sourceStep trivial held
    obtain ⟨wPure, pureStep, _⟩ := executed Arm.ArmState.default
    have sameExecution := Option.some.inj (pureStep.symm.trans machineStep)
    have regEq := (SeqEnd.fall.inj sameExecution).1
    have worldEq := (SeqEnd.fall.inj sameExecution).2
    rw [← regEq] at machineStep sourceHeld
    rw [← worldEq] at machineStep
    have literal : (⟨.i8, 9⟩ : Clif.Val) = .ofInt .i8 9 := by decide +kernel
    exact ⟨result, event, record, ρ', rfl, exampleScope, exampleDominated, events, records,
      context, current, rfl, by rw [resultResolved]; change ¬ VHolds (.ofInt .i8 77) 0; unfold VHolds; decide +kernel,
      executed, by rw [← literal]; simpa only [resultResolved] using value, heldAfter, fr', wPure, sourceStep, machineStep, sourceHeld⟩

end Backend.Stock.Proof
