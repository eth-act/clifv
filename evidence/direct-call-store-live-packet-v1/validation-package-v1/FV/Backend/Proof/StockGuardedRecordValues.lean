import FV.Backend.Proof.StockAvailableValues
import FV.Backend.Proof.StockRecordIntervals
import FV.Backend.Proof.StockDemandMono

/-! Source-availability-guarded value transfer for actual fresh-result records. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

/-- Family-specific execution and fresh-def bounds combine with whole-run
binding, final resolution and availability. The demanded/available set can change
at the source statement without requiring its old result value beforehand. -/
theorem stock_lower_fresh_record_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {inst : Clif.Inst} {z a d : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some inst)
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (output : step.results = [[.vreg d .int]]) (fresh : record.input.base.nextVreg ≤ d)
    (demand : ∀ y, Demanded record.input y → Demanded record.output.state y)
    {W : Type} {sem : ISem CV W} {fr : Clif.Frame} {ρ ρ' : Nat → CV} {w w' : W} {v : Clif.Val}
    (held : ValuesHeld (fun y => Demanded record.output.state y ∧
      y ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    (defs : ∀ m ∈ record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1))), ∀ key ∈ vdefs m,
        record.input.base.nextVreg ≤ key ∧ key < record.output.state.base.nextVreg)
    (executed : seqRun sem (record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ w = some (.fall ρ' w'))
    (value : VHolds v (ρ' d)) :
    ValuesHeld (fun y => Demanded record.input y ∧
      y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx (withValue fr z v)
        (fun k => ρ' (aliasNum result.final.alias k)) := by
  have resolved := (stock_lower_record_fresh_result run scope dominated.ssa events records source clif
    results mapped recorded emitted output fresh).2
  have maps := (stock_lower_record_context run scope events).2.1
  intro y required val lookup
  by_cases equal : y = z
  · subst y
    simp only [withValue, eq_self, ite_true] at lookup
    cases lookup
    exact ⟨a, mapped, by change VHolds v (ρ' (aliasNum result.final.alias a)); rw [resolved]; exact value⟩
  · simp only [withValue, ite_eq_right equal] at lookup
    have before := available_before_of_after_not_result block statement required.2
      (by simpa only [statementResults, List.mem_singleton] using equal)
    obtain ⟨key, map, old⟩ := held y ⟨demand y required.1, before⟩ val lookup
    have preserved := stock_lower_available_fresh_frame run scope dominated events records block statement current
      before (by rw [← maps]; exact map) defs executed
    exact ⟨key, map, by change VHolds val (ρ' (aliasNum result.final.alias key)); rw [preserved]; exact old⟩

/-- The original guarded transfer remains available. This variant derives
its demand premise from successful actual whole-driver record execution. -/
theorem stock_lower_fresh_record_values_auto_demand {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {inst : Clif.Inst} {z a d : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some inst)
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (output : step.results = [[.vreg d .int]]) (fresh : record.input.base.nextVreg ≤ d)
    {W : Type} {sem : ISem CV W} {fr : Clif.Frame} {ρ ρ' : Nat → CV} {w w' : W} {v : Clif.Val}
    (held : ValuesHeld (fun y => Demanded record.output.state y ∧
      y ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    (defs : ∀ m ∈ record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1))), ∀ key ∈ vdefs m,
        record.input.base.nextVreg ≤ key ∧ key < record.output.state.base.nextVreg)
    (executed : seqRun sem (record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ w = some (.fall ρ' w'))
    (value : VHolds v (ρ' d)) :
    ValuesHeld (fun y => Demanded record.input y ∧
      y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx (withValue fr z v)
        (fun k => ρ' (aliasNum result.final.alias k)) := by
  have demand : ∀ y, Demanded record.input y → Demanded record.output.state y := by
    intro y wanted zero
    have count := stock_lower_record_demand_mono run events records recorded emitted y
    change record.output.state.demand[y]! = 0 at zero
    rw [zero] at count
    exact wanted (Nat.eq_zero_of_le_zero count)
  exact stock_lower_fresh_record_values run scope dominated events records block statement current
    source clif results statementResults mapped recorded emitted output fresh demand held defs executed value

/-- A successful source instruction with one result has exactly the register
update used by guarded value transfer, regardless of its body/memory changes. -/
theorem source_single_result_values {env : Clif.Env} {cp : Clif.Program} {ctx : Ctx} {i z : Nat}
    {info : IInfo} {inst : Clif.Inst} {fr fr' : Clif.Frame} {cm cm' : Clif.Mem} {v : Clif.Val}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some inst) (results : info.results = [z])
    (step : SourceInstResult env cp ctx i (fr, cm) (fr', cm'))
    (evaluated : instOutcome env cp fr cm inst = .ok ([v], cm'))
    {needed : Nat → Prop} {ρ : Nat → CV} (held : ValuesHeld needed ctx (withValue fr z v) ρ) :
    ValuesHeld needed ctx fr' ρ := by
  obtain ⟨info', inst', vals, regs, rest, lookup, original, _, eval, written, frame⟩ := step
  have sameInfo := Option.some.inj (lookup.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst'
  have values := (Prod.mk.inj (Clif.Res.ok.inj (eval.symm.trans evaluated))).1
  rw [values, results] at written
  simp only [Clif.Regs.setMany_cons, Clif.Regs.setMany_nil, Option.some.injEq] at written
  subst regs
  change fr' = _ at frame
  rw [frame]
  exact held

attribute [local semireducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock
private def exampleFunction : Clif.Function := {
  name := "guarded_add_record"
  sig := { params := [⟨.i64, .none, .normal⟩, ⟨.i64, .none, .normal⟩], returns := [⟨.i64, .none, .normal⟩], callConv := some .systemV }
  blocks := [{ id := 0, params := [(7, .i64), (31, .i64)], body := [⟨[100], .binary .iadd .i64 7 31⟩], term := .ret [100] }] }
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
        change y ∈ [7, 31] at member
        change y ∈ (([7, 31] ++ (availIn exampleFunction ctx).getD 0 [] ++ []).filter (fun x => decide (x ∉ [100])))
        simp only [List.mem_filter, decide_eq_true_eq, List.append_nil]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp
      · intro y member
        change y ∈ [100] at member
        have equal := List.mem_singleton.mp member
        subst y
        change 100 ∈ (([7, 31] ++ (availIn exampleFunction ctx).getD 0 [] ++ [100]).filter
          (fun x => decide (x ∉ ([] : List Nat))))
        simp
    | succ bi => simp [exampleFunction] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bounds := (inFix_fixOk (f := exampleFunction) (ctx := ctx) (gn := id)).cand tl x available
    have length : exampleFunction.blocks.length = 1 := rfl
    omega
private theorem beforeAvailable (ctx : Ctx) (y : Nat) :
    y ∈ availOf exampleFunction (availIn exampleFunction ctx) 0 0 ↔ y = 7 ∨ y = 31 := by
  have noEntry : y ∉ (availIn exampleFunction ctx).getD 0 [] := by
    intro member
    have bound := (inFix_fixOk (f := exampleFunction) (ctx := ctx) (gn := id)).cand 0 y member
    omega
  rw [mem_av (show exampleFunction.blocks[0]? = some
    ({id := 0, params := [(7, .i64), (31, .i64)], body := [⟨[100], .binary .iadd .i64 7 31⟩], term := .ret [100]} : Clif.Block) from rfl)]
  constructor
  · intro available
    rcases available.1 with param | entry | ⟨k, stm, earlier, _, _⟩
    · simpa using param
    · exact False.elim (noEntry entry)
    · omega
  · intro equal
    rcases equal with rfl | rfl
    all_goals
      refine ⟨Or.inl (by simp), ?_⟩
      intro ⟨k, stm, _, statement, member⟩
      cases k <;> simp at statement
      subst stm
      simp at member
private def exampleCode : MInst := .aluRRR .add .size64 (.vreg 195 .int) (.vreg 192 .int) (.vreg 193 .int)
private def exampleFrame : Clif.Frame := {
  func := exampleFunction
  regs := fun x => if x = 7 then some (.ofInt .i64 7) else if x = 31 then some (.ofInt .i64 5)
    else if x = 100 then some (.ofInt .i64 99) else none
  slots := [], body := [⟨[100], .binary .iadd .i64 7 31⟩], term := .ret [100] }
private def exampleRegs (n : Nat) : CV := if n = 192 then 7 else if n = 193 then 5 else 0
private def exampleNext : Nat → CV := upd exampleRegs 195 12
private theorem observed : (Stock.lower exampleFunction).toOption.map (fun result =>
    (aliasNum result.final.alias 192, aliasNum result.final.alias 193, aliasNum result.final.alias 195,
      result.blockScans.toList.any (fun event => event.output.records.any (fun record =>
        record.inst == 0 && record.input.base.nextVreg == 195 && record.output.state.base.nextVreg == 196 &&
        record.input.demand.size == 101 && record.input.demand[100]! != 0 &&
        decide (record.output.state.demand = ((record.input.mark 7).mark 31).demand) &&
        decide ((event.ctx.insts[0]?).map (fun info => (info.clif, info.results)) = some (some (.binary .iadd .i64 7 31), [100])) &&
        decide (event.ctx.valueReg? 7 = some (.vreg 192 .int)) && decide (event.ctx.valueReg? 31 = some (.vreg 193 .int)) &&
        decide (event.ctx.valueReg? 100 = some (.vreg 194 .int)) &&
        record.output.step.any (fun step => step.decision == .emitted && decide (step.results = [[.vreg 195 .int]])) &&
        decide (record.output.emitted = #[exampleCode]))))) = some (192, 193, 195, true) := by
  decide +kernel

/-- Complete actual add execution replaces stale source99 by12, preserves
arguments7/5, and establishes the newly available demanded result100. -/
theorem stock_lower_fresh_record_values_witness :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord),
      Stock.lower exampleFunction = .ok result ∧ LowerScope exampleFunction ∧ Dominated exampleFunction ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧ record.inst = 0 ∧
      exampleFrame.regs 100 = some (.ofInt .i64 99) ∧
      seqRun ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1))))
          exampleRegs Arm.ArmState.default = some (.fall exampleNext Arm.ArmState.default) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf exampleFunction (availIn exampleFunction result.ctx) 0 1) event.ctx
          (withValue exampleFrame 100 (.ofInt .i64 12)) (fun k => exampleNext (aliasNum result.final.alias k)) ∧
      VHolds (.ofInt .i64 12) (exampleNext (aliasNum result.final.alias 194)) ∧
      exampleNext 192 = 7 ∧ exampleNext 193 = 5 ∧
      ∃ fr', SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (exampleFrame, Clif.Mem.empty) (fr', Clif.Mem.empty) ∧
        ValuesHeld (fun y => Demanded record.input y ∧
          y ∈ availOf exampleFunction (availIn exampleFunction result.ctx) 0 1) event.ctx fr'
            (fun k => exampleNext (aliasNum result.final.alias k)) := by
  have actual := observed
  cases run : Stock.lower exampleFunction with
  | error e => simp only [run, Except.toOption, Option.map_none] at actual; cases actual
  | ok result =>
    simp only [run, Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at actual
    obtain ⟨xResolved, yResolved, dResolved, found⟩ := actual
    obtain ⟨event, events, record, records, current, frontier, upper, demandSize, wantedResult,
        demandEq, sourceData, xMap, yMap, mapped, stepData, code⟩ :=
      (by simpa only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq, and_assoc] using found :
        ∃ event ∈ result.blockScans.toList, ∃ record ∈ event.output.records,
          record.inst = 0 ∧ record.input.base.nextVreg = 195 ∧ record.output.state.base.nextVreg = 196 ∧
          record.input.demand.size = 101 ∧ record.input.demand[100]! ≠ 0 ∧
          record.output.state.demand = ((record.input.mark 7).mark 31).demand ∧
          (event.ctx.insts[0]?).map (fun info => (info.clif, info.results)) = some (some (.binary .iadd .i64 7 31), [100]) ∧
          event.ctx.valueReg? 7 = some (.vreg 192 .int) ∧ event.ctx.valueReg? 31 = some (.vreg 193 .int) ∧
          event.ctx.valueReg? 100 = some (.vreg 194 .int) ∧
          record.output.step.any (fun step => step.decision == .emitted && decide (step.results = [[.vreg 195 .int]])) = true ∧
          record.output.emitted = #[exampleCode])
    obtain ⟨info, source, clif, results⟩ := (by
      simpa only [Option.map_eq_some_iff, Prod.mk.injEq] using sourceData :
        ∃ info, event.ctx.insts[0]? = some info ∧ info.clif = some (.binary .iadd .i64 7 31) ∧ info.results = [100])
    obtain ⟨step, recorded, emitted, outputs⟩ := (by
      simpa only [Option.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using stepData :
        ∃ step, record.output.step = some step ∧ step.decision = .emitted ∧ step.results = [[.vreg 195 .int]])
    have source' : event.ctx.insts[record.inst]? = some info := by simpa only [current] using source
    have resolve := (stock_lower_record_fresh_result run exampleScope exampleDominated.ssa events records
      source' clif results mapped recorded emitted outputs (by rw [frontier]; exact Nat.le_refl _)).2
    have mappedCode : record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1))) = [exampleCode] := by
      rw [code]
      change [exampleCode.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1))] = [exampleCode]
      congr 1
      change MInst.aluRRR .add .size64
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1) (.vreg 195 .int))
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1) (.vreg 192 .int))
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1) (.vreg 193 .int)) = _
      rw [resolve_vreg, resolve_vreg, resolve_vreg]
      change MInst.aluRRR .add .size64 (.vreg (aliasNum result.final.alias 195) .int)
        (.vreg (aliasNum result.final.alias 192) .int) (.vreg (aliasNum result.final.alias 193) .int) = _
      rw [dResolved, xResolved, yResolved]
      rfl
    have executed : seqRun ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) exampleRegs Arm.ArmState.default =
        some (.fall exampleNext Arm.ArmState.default) := by rw [mappedCode]; rfl
    have defs : ∀ m ∈ record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1))), ∀ key ∈ vdefs m,
        record.input.base.nextVreg ≤ key ∧ key < record.output.state.base.nextVreg := by
      rw [mappedCode]
      intro m member key defined
      have equal := List.mem_singleton.mp member
      subst m
      change key ∈ [195] at defined
      have equal := List.mem_singleton.mp defined
      subst key
      rw [frontier, upper]
      omega
    have held : ValuesHeld (fun y => Demanded record.output.state y ∧
        y ∈ availOf exampleFunction (availIn exampleFunction result.ctx) 0 0) event.ctx exampleFrame
          (fun k => exampleRegs (aliasNum result.final.alias k)) := by
      intro y required val lookup
      rcases (beforeAvailable result.ctx y).mp required.2 with rfl | rfl
      · change some (Clif.Val.ofInt .i64 7) = some val at lookup
        cases lookup
        refine ⟨192, xMap, ?_⟩
        change VHolds (.ofInt .i64 7) (exampleRegs (aliasNum result.final.alias 192))
        rw [xResolved]
        unfold VHolds exampleRegs
        decide +kernel
      · change some (Clif.Val.ofInt .i64 5) = some val at lookup
        cases lookup
        refine ⟨193, yMap, ?_⟩
        change VHolds (.ofInt .i64 5) (exampleRegs (aliasNum result.final.alias 193))
        rw [yResolved]
        unfold VHolds exampleRegs
        decide +kernel
    have value : VHolds (.ofInt .i64 12) (exampleNext 195) := by unfold VHolds exampleNext upd exampleRegs; decide +kernel
    have installed := stock_lower_fresh_record_values_auto_demand run exampleScope exampleDominated events records
      (bi := 0) (j := 0) (b := exampleFunction.blocks[0]!) (stm := ⟨[100], .binary .iadd .i64 7 31⟩)
      rfl rfl (by simpa only [blockStart, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add] using current)
      source' clif results rfl mapped recorded emitted outputs (by rw [frontier]; exact Nat.le_refl _)
      held defs executed value
    let fr' : Clif.Frame := {exampleFrame with regs := exampleFrame.regs.set 100 (.ofInt .i64 12), body := []}
    have sourceEval : instOutcome Clif.Env.empty {funcs := []} exampleFrame Clif.Mem.empty
        (.binary .iadd .i64 7 31) = .ok ([.ofInt .i64 12], Clif.Mem.empty) := rfl
    have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (exampleFrame, Clif.Mem.empty) (fr', Clif.Mem.empty) :=
      ⟨info, .binary .iadd .i64 7 31, [.ofInt .i64 12], exampleFrame.regs.set 100 (.ofInt .i64 12), [],
        source', clif, by rw [results]; rfl, sourceEval, by rw [results]; rfl, rfl⟩
    have sourceHeld := source_single_result_values source' clif results sourceStep sourceEval installed
    refine ⟨result, event, record, rfl, exampleScope, exampleDominated, events, records, current, rfl,
      executed, installed, ?_, rfl, rfl, fr', sourceStep, sourceHeld⟩
    rw [resolve]
    exact value

end Backend.Stock.Proof
