import FV.Backend.Proof.StockDemand
import FV.Backend.Proof.StockDemandExtent

/-! Derive selected ALU operands from the actual guarded value invariant. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

private theorem DFGViewEq.availIn_eq {ctx original : Ctx}
    (view : DFGViewEq ctx original) (f : Clif.Function) :
    availIn f ctx = availIn f original := by
  have args : defArgs ctx = defArgs original := by
    funext x
    simp only [defArgs, Ctx.defInst?, view.valDef, view.insts]
  have users : fUsers ctx = fUsers original := by
    simp only [fUsers, usersN, args, view.valDef]
  have bytes : fInB0 f ctx id = fInB0 f original id := by
    unfold fInB0
    rw [view.valDef]
  have work : fWork0 f ctx id = fWork0 f original id := by
    simp only [fWork0, view.valDef, bytes, args]
  simp only [availIn, inFix_eq, users, bytes, work, view.valDef]

/-- The unchanged source dominance condition supplies every actual source
operand at the recorded statement boundary, through the retained original DFG. -/
theorem stock_lower_record_args_available {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {inst : Clif.Inst}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some inst) :
    ∀ y ∈ Driver.instArgs inst, y ∈ availOf f (availIn f result.ctx) bi j := by
  obtain ⟨context, maps, sources⟩ := stock_lower_record_context run scope events
  have globalSource := sources _ _ _ source clif
  rw [current] at globalSource
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, nodeBi, data, core, build, ordered, initial, empty, parts, folded,
    final, prefixRun, nodeRun, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original, st0, old, spec, view⟩ := buildCtx_source build
  obtain ⟨other, otherSource, otherClif, otherResults⟩ := spec.facts.stmt bi b j stm block statement
  have actualSource : original.insts[blockStart f bi + j]? = some info := by
    rw [← view.insts]
    exact globalSource
  have same := Option.some.inj (otherSource.symm.trans actualSource)
  subst other
  have instSame := Option.some.inj (otherClif.symm.trans clif)
  intro y member
  have use : y ∈ Driver.instArgs stm.inst := by rw [instSame]; exact member
  have available := (dominated.uses original ranges st0 old bi b block).1 j stm statement y use
  simpa only [view.availIn_eq f] using available

/-- Successful actual add/subtract requests put both source operands in the
demanded/available guard. Whole-run extent and source dominance derive all bounds. -/
theorem stock_lower_alu_operand_coverage {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {z a x y n : Nat} {ty : Clif.Ty} (subtract : Bool) (width : ty.width ≤ 64)
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y))
    (results : info.results = [z]) (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {next : State} {out : V} {evalTrace : Array RuleId} {trace : List RuleId}
    (evalRun : (evalExpr program (Stock.sem event.ctx) {} (n + 40)
      (if subtract then rule_lower_801 else rule_lower_86).rhs
      (env3 (.ty (.int ty.width)) (.value x) (.value y))).run
        (scanState record.input record.inst, #[]) = .ok (some out, next, evalTrace))
    (rootRun : Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
      .ok (some out, next, trace)) :
    ∀ key, key = x ∨ key = y → Demanded record.output.state key ∧
      key ∈ availOf f (availIn f result.ctx) bi j := by
  obtain ⟨nx, ny, mx, my, _, _, _, demands⟩ := stock_lower_alu_record_shape run scope events records
    subtract width source results mapped recorded emitted evalRun rootRun
  have bx := (Extent.lower_mapped_demand_bounds run scope events records mx).1
  have by_ := (Extent.lower_mapped_demand_bounds run scope events records my).1
  have available := stock_lower_record_args_available run scope dominated events block statement current source clif
  have requested (key : Nat) (bound : key < record.input.demand.size) (member : key ∈ [x, y]) :
      Demanded record.output.state key := by
    have wanted := (demanded_markList_iff record.input [x, y] key bound).mpr (Or.inl member)
    change record.output.state.demand[key]! ≠ 0
    rw [demands]
    exact wanted
  intro key member
  rcases member with rfl | rfl
  · exact ⟨requested key bx (by simp), available key (by simp [Driver.instArgs])⟩
  · exact ⟨requested key by_ (by simp), available key (by simp [Driver.instArgs])⟩

/-- Keep the original transfer interface. This variant derives its separate
operand-value premise from the guarded invariant and actual driver execution. -/
theorem stock_lower_alu_available_values_auto_operands {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {z a x y n : Nat} {ty : Clif.Ty} (subtract : Bool) (width : ty.width ≤ 64)
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {next : State} {out : V} {evalTrace : Array RuleId} {trace : List RuleId}
    (evalRun : (evalExpr program (Stock.sem event.ctx) {} (n + 40)
      (if subtract then rule_lower_801 else rule_lower_86).rhs
      (env3 (.ty (.int ty.width)) (.value x) (.value y))).run
        (scanState record.input record.inst, #[]) = .ok (some out, next, evalTrace))
    (rootRun : Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
      .ok (some out, next, trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u v : BitVec ty.width} (sourceX : fr.getAs x ty = .ok u) (sourceY : fr.getAs y ty = .ok v) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty, Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩ (ρ' record.input.base.nextVreg) ∧
      (∀ key, key ≠ record.input.base.nextVreg → ρ' key = ρ key) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          (withValue fr z ⟨ty, Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩)
          (fun k => ρ' (aliasNum result.final.alias k)) := by
  have coverage := stock_lower_alu_operand_coverage run scope dominated events records
    block statement current subtract width source clif results mapped recorded emitted evalRun rootRun
  have operands := held.mono coverage
  exact stock_lower_alu_available_values run scope dominated events records block statement current
    subtract width source clif results statementResults mapped recorded emitted evalRun rootRun
    refines operands held sourceX sourceY

attribute [local semireducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock
private def exampleFunction (subtract : Bool) : Clif.Function := {
  name := "guarded_add_record"
  sig := { params := [⟨.i64, .none, .normal⟩, ⟨.i64, .none, .normal⟩], returns := [⟨.i64, .none, .normal⟩], callConv := some .systemV }
  blocks := [{ id := 0, params := [(7, .i64), (31, .i64)], body := [⟨[100], .binary (if subtract then .isub else .iadd) .i64 7 31⟩], term := .ret [100] }] }
private theorem exampleScope (subtract : Bool) : LowerScope (exampleFunction subtract) := lowerScope_of (by cases subtract <;> decide +kernel)
private theorem exampleDominated (subtract : Bool) : Dominated (exampleFunction subtract) := by
  constructor
  · cases subtract <;> decide +kernel
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
        change y ∈ (([7, 31] ++ (availIn (exampleFunction subtract) ctx).getD 0 [] ++ []).filter (fun x => decide (x ∉ [100])))
        simp only [List.mem_filter, decide_eq_true_eq, List.append_nil]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp
      · intro y member
        change y ∈ [100] at member
        have equal := List.mem_singleton.mp member
        subst y
        change 100 ∈ (([7, 31] ++ (availIn (exampleFunction subtract) ctx).getD 0 [] ++ [100]).filter
          (fun x => decide (x ∉ ([] : List Nat))))
        simp
    | succ bi => simp [exampleFunction] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bounds := (inFix_fixOk (f := (exampleFunction subtract)) (ctx := ctx) (gn := id)).cand tl x available
    have length : (exampleFunction subtract).blocks.length = 1 := rfl
    omega
private theorem beforeAvailable (subtract : Bool) (ctx : Ctx) (y : Nat) :
    y ∈ availOf (exampleFunction subtract) (availIn (exampleFunction subtract) ctx) 0 0 ↔ y = 7 ∨ y = 31 := by
  have noEntry : y ∉ (availIn (exampleFunction subtract) ctx).getD 0 [] := by
    intro member
    have bound := (inFix_fixOk (f := (exampleFunction subtract)) (ctx := ctx) (gn := id)).cand 0 y member
    omega
  rw [mem_av (show (exampleFunction subtract).blocks[0]? = some
    ({id := 0, params := [(7, .i64), (31, .i64)], body := [⟨[100], .binary (if subtract then .isub else .iadd) .i64 7 31⟩], term := .ret [100]} : Clif.Block) from rfl)]
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
private def exampleFrame (subtract : Bool) : Clif.Frame := {
  func := (exampleFunction subtract)
  regs := fun x => if x = 7 then some (.ofInt .i64 7) else if x = 31 then some (.ofInt .i64 5)
    else if x = 100 then some (.ofInt .i64 99) else none
  slots := [], body := [⟨[100], .binary (if subtract then .isub else .iadd) .i64 7 31⟩], term := .ret [100] }
private def exampleRegs (n : Nat) : CV := if n = 192 then 7 else if n = 193 then 5 else 0
private instance : DecidableEq V := fun a b => decidable_of_iff ((a == b) = true) beq_iff_eq

private theorem of_toOption {ε α : Type} {e : Except ε α} {a : α}
    (h : e.toOption = some a) : e = .ok a := by
  cases e with
  | error err => cases h
  | ok value =>
    simp only [Except.toOption, Option.some.injEq] at h
    subst value
    rfl

private theorem observed (subtract : Bool) :
    (Stock.lower (exampleFunction subtract)).toOption.map (fun result =>
      (aliasNum result.final.alias 192, aliasNum result.final.alias 193,
        result.blockScans.toList.any (fun event => event.output.records.any (fun record =>
          record.inst == 0 && record.input.base.nextVreg == 195 &&
          decide ((event.ctx.insts[0]?).map (fun info => (info.clif, info.results)) =
            some (some (.binary (if subtract then .isub else .iadd) .i64 7 31), [100])) &&
          decide (event.ctx.valueReg? 7 = some (.vreg 192 .int)) &&
          decide (event.ctx.valueReg? 31 = some (.vreg 193 .int)) &&
          decide (event.ctx.valueReg? 100 = some (.vreg 194 .int)) &&
          record.output.step.any (fun step => step.decision == .emitted) &&
          ((evalExpr program (Stock.sem event.ctx) {} 40
            (if subtract then rule_lower_801 else rule_lower_86).rhs
            (env3 (.ty (.int 64)) (.value 7) (.value 31))).run
              (scanState record.input record.inst, #[])).toOption.any (fun evaluated =>
                decide (evaluated.1 = some (.regsVec [[.vreg 195 .int]])) &&
                decide ((Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst)).toOption =
                  some (evaluated.1, evaluated.2.1,
                    evaluated.2.2.toList ++ [(if subtract then rule_lower_801 else rule_lower_86).id]))))))) =
        some (192, 193, true) := by
  cases subtract <;> decide +kernel

/-- Complete Stock add/subtract runs with sparse source IDs establish12/2,
preserve both arguments and transfer the available demanded set to the actual
source-step frame without assuming code, execution, fresh definitions or aliases. -/
theorem stock_lower_alu_auto_values_witness (subtract : Bool) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (ρ' : Nat → CV),
      Stock.lower (exampleFunction subtract) = .ok result ∧ LowerScope (exampleFunction subtract) ∧
      Dominated (exampleFunction subtract) ∧ event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.inst = 0 ∧ (exampleFrame subtract).regs 100 = some (.ofInt .i64 99) ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) exampleRegs ρ' ∧
      VHolds (.ofInt .i64 (if subtract then 2 else 12)) (ρ' 195) ∧ ρ' 192 = 7 ∧ ρ' 193 = 5 ∧
      ∃ fr', SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (exampleFrame subtract, Clif.Mem.empty) (fr', Clif.Mem.empty) ∧
        ValuesHeld (fun y => Demanded record.input y ∧
          y ∈ availOf (exampleFunction subtract) (availIn (exampleFunction subtract) result.ctx) 0 1) event.ctx fr'
            (fun k => ρ' (aliasNum result.final.alias k)) := by
  have actual := observed subtract
  cases run : Stock.lower (exampleFunction subtract) with
  | error e => simp only [run, Except.toOption, Option.map_none] at actual; cases actual
  | ok result =>
    have successful : (Stock.lower (exampleFunction subtract)).toOption = some result := by rw [run]; rfl
    rw [successful, Option.map_some] at actual
    simp only [Option.some.injEq, Prod.mk.injEq] at actual
    obtain ⟨xResolved, yResolved, found⟩ := actual
    obtain ⟨event, events, record, records, current, frontier, sourceData, xMap, yMap, mapped, stepData, rhsData⟩ :=
      (by simpa only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using found :
        ∃ event ∈ result.blockScans.toList, ∃ record ∈ event.output.records,
          record.inst = 0 ∧ record.input.base.nextVreg = 195 ∧
          (event.ctx.insts[0]?).map (fun info => (info.clif, info.results)) =
            some (some (.binary (if subtract then .isub else .iadd) .i64 7 31), [100]) ∧
          event.ctx.valueReg? 7 = some (.vreg 192 .int) ∧ event.ctx.valueReg? 31 = some (.vreg 193 .int) ∧
          event.ctx.valueReg? 100 = some (.vreg 194 .int) ∧
          record.output.step.any (fun step => step.decision == .emitted) = true ∧
          ((evalExpr program (Stock.sem event.ctx) {} 40
            (if subtract then rule_lower_801 else rule_lower_86).rhs
            (env3 (.ty (.int 64)) (.value 7) (.value 31))).run
              (scanState record.input record.inst, #[])).toOption.any (fun evaluated =>
                decide (evaluated.1 = some (.regsVec [[.vreg 195 .int]])) &&
                decide ((Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst)).toOption =
                  some (evaluated.1, evaluated.2.1,
                    evaluated.2.2.toList ++ [(if subtract then rule_lower_801 else rule_lower_86).id]))) = true)
    obtain ⟨info, source, clif, results⟩ := (by
      simpa only [Option.map_eq_some_iff, Prod.mk.injEq] using sourceData :
        ∃ info, event.ctx.insts[0]? = some info ∧
          info.clif = some (.binary (if subtract then .isub else .iadd) .i64 7 31) ∧ info.results = [100])
    obtain ⟨step, recorded, emitted⟩ := (by
      simpa only [Option.any_eq_true, beq_iff_eq] using stepData :
        ∃ step, record.output.step = some step ∧ step.decision = .emitted)
    obtain ⟨evaluated, evalOption, outEq, rootOption⟩ := (by
      simpa only [Option.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] using rhsData :
        ∃ evaluated, ((evalExpr program (Stock.sem event.ctx) {} 40
            (if subtract then rule_lower_801 else rule_lower_86).rhs
            (env3 (.ty (.int 64)) (.value 7) (.value 31))).run
              (scanState record.input record.inst, #[])).toOption = some evaluated ∧
          evaluated.1 = some (.regsVec [[.vreg 195 .int]]) ∧
          (Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst)).toOption =
            some (evaluated.1, evaluated.2.1,
              evaluated.2.2.toList ++ [(if subtract then rule_lower_801 else rule_lower_86).id]))
    have evalRun : (evalExpr program (Stock.sem event.ctx) {} 40
        (if subtract then rule_lower_801 else rule_lower_86).rhs
        (env3 (.ty (.int 64)) (.value 7) (.value 31))).run
          (scanState record.input record.inst, #[]) = .ok evaluated := by
      exact of_toOption evalOption
    have rootRun := of_toOption rootOption
    obtain ⟨out, next, trace⟩ := evaluated
    simp only at outEq
    subst out
    have source' : event.ctx.insts[record.inst]? = some info := by simpa only [current] using source
    have operandHeld : ValuesHeld (fun y => y = 7 ∨ y = 31) event.ctx (exampleFrame subtract)
        (fun k => exampleRegs (aliasNum result.final.alias k)) := by
      intro y required val lookup
      rcases required with rfl | rfl
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
    have held : ValuesHeld (fun y => Demanded record.output.state y ∧
        y ∈ availOf (exampleFunction subtract) (availIn (exampleFunction subtract) result.ctx) 0 0)
        event.ctx (exampleFrame subtract) (fun k => exampleRegs (aliasNum result.final.alias k)) :=
      fun y required => operandHeld y ((beforeAvailable subtract result.ctx y).mp required.2)
    have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w', h, SameWorld.refl _ _⟩
    have sourceX : (exampleFrame subtract).getAs 7 .i64 = .ok (BitVec.ofInt 64 7) := rfl
    have sourceY : (exampleFrame subtract).getAs 31 .i64 = .ok (BitVec.ofInt 64 5) := rfl
    obtain ⟨ρ', executed, value, kept, installed⟩ := stock_lower_alu_available_values_auto_operands run
      (exampleScope subtract) (exampleDominated subtract) events records
      (bi := 0) (j := 0) (b := (exampleFunction subtract).blocks[0]!)
      (stm := ⟨[100], .binary (if subtract then .isub else .iadd) .i64 7 31⟩)
      rfl rfl (by simpa only [blockStart, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add] using current)
      subtract (by decide) source' clif results rfl mapped recorded emitted
      (n := 0) evalRun rootRun self held sourceX sourceY
    have literal : (⟨Clif.Ty.i64, Clif.Sem.binary (if subtract then .isub else .iadd)
        (BitVec.ofInt 64 7) (BitVec.ofInt 64 5)⟩ : Clif.Val) = .ofInt .i64 (if subtract then 2 else 12) := by
      cases subtract <;> decide +kernel
    rw [literal] at value installed
    let fr' : Clif.Frame := {exampleFrame subtract with
      regs := (exampleFrame subtract).regs.set 100 (.ofInt .i64 (if subtract then 2 else 12)), body := []}
    have sourceEval : instOutcome Clif.Env.empty {funcs := []} (exampleFrame subtract) Clif.Mem.empty
        (.binary (if subtract then .isub else .iadd) .i64 7 31) =
          .ok ([.ofInt .i64 (if subtract then 2 else 12)], Clif.Mem.empty) := by cases subtract <;> rfl
    have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (exampleFrame subtract, Clif.Mem.empty) (fr', Clif.Mem.empty) :=
      ⟨info, .binary (if subtract then .isub else .iadd) .i64 7 31,
        [.ofInt .i64 (if subtract then 2 else 12)],
        (exampleFrame subtract).regs.set 100 (.ofInt .i64 (if subtract then 2 else 12)), [],
        source', clif, by rw [results]; rfl, sourceEval, by rw [results]; rfl, rfl⟩
    have sourceHeld := source_single_result_values source' clif results sourceStep sourceEval installed
    refine ⟨result, event, record, ρ', rfl, exampleScope subtract, exampleDominated subtract,
      events, records, current, rfl, executed, ?_, ?_, ?_, fr', sourceStep, sourceHeld⟩
    · simpa only [frontier] using value
    · exact (kept 192 (by rw [frontier]; decide)).trans rfl
    · exact (kept 193 (by rw [frontier]; decide)).trans rfl

end Backend.Stock.Proof
