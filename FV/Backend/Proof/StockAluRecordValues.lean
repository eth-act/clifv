import FV.Backend.Proof.StockRequestSuccess
import FV.Backend.Proof.StockGuardedRecordValues

/-! Selected add/subtract value transfer for actual retained Stock records. -/
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

private theorem scan_empty (st : State) (i : Nat) :
    (scanState st i).base.emitted = #[] := by
  unfold scanState
  dsimp only
  split <;> rfl

private theorem scan_frontier (st : State) (i : Nat) :
    (scanState st i).base.nextVreg = st.base.nextVreg := by
  unfold scanState
  dsimp only
  split <;> rfl

private theorem rhs_observed (subtract : Bool) (ctx : Ctx) {x y w n : Nat} (hw : w ≤ 64)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr program (Stock.sem ctx) {} (n + 40)
      (if subtract then rule_lower_801 else rule_lower_86).rhs
      (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) = .ok (some out, next, trace)) :
    ∃ rx ry, ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧
      out = .regsVec [[(st.base.fresh .int).1]] ∧
      next = {(st.mark x).mark y with base := (st.base.fresh .int).2.emit (.aluRRR
        (if subtract then .sub else .add) (szOf w) (st.base.fresh .int).1 rx ry)} := by
  cases subtract
  · exact stock_rhs_86_observed data_program ctx rfl hw run
  · exact stock_rhs_801_observed data_program ctx rfl hw run

/-- Actual retained emitted records with successful selected add/subtract RHS
and named-root receipts have exactly one fresh ALU instruction. Register mappings,
output, allocation endpoints and marked demands are derived from those runs. -/
theorem stock_lower_alu_record_shape {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {z a x y w n : Nat} (subtract : Bool) (width : w ≤ 64)
    (source : event.ctx.insts[record.inst]? = some info) (results : info.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {next : State} {out : V} {evalTrace : Array RuleId} {trace : List RuleId}
    (evalRun : (evalExpr program (Stock.sem event.ctx) {} (n + 40)
      (if subtract then rule_lower_801 else rule_lower_86).rhs
      (env3 (.ty (.int w)) (.value x) (.value y))).run
        (scanState record.input record.inst, #[]) = .ok (some out, next, evalTrace))
    (rootRun : Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
      .ok (some out, next, trace)) :
    ∃ nx ny, event.ctx.valueReg? x = some (.vreg nx .int) ∧ event.ctx.valueReg? y = some (.vreg ny .int) ∧
      step.results = [[.vreg record.input.base.nextVreg .int]] ∧
      record.output.emitted = #[.aluRRR (if subtract then .sub else .add) (szOf w)
        (.vreg record.input.base.nextVreg .int) (.vreg nx .int) (.vreg ny .int)] ∧
      record.output.state.base.nextVreg = record.input.base.nextVreg + 1 ∧
      record.output.state.demand = ((record.input.mark x).mark y).demand := by
  obtain ⟨rx, ry, mx, my, outEq, nextEq⟩ := rhs_observed subtract event.ctx width evalRun
  have context := (stock_lower_record_context run scope events).1
  obtain ⟨nx, rfl⟩ := context.valueReg x rx mx
  obtain ⟨ny, rfl⟩ := context.valueReg y ry my
  have installed := bindResults_virtual event.ctx next [(z, a, record.input.base.nextVreg)] (by
    intro p member
    have equal := List.mem_singleton.mp member
    subst p
    exact mapped)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at installed
  have outEq' : out = .regsVec [[.vreg record.input.base.nextVreg .int]] := by
    simpa only [LState.fresh, scan_frontier] using outEq
  rw [outEq'] at rootRun
  have infoBang : event.ctx.insts[record.inst]! = info := by simp only [getElem!_def, source]
  have emitter : emitInstruction event.ctx record.inst (scanState record.input record.inst) =
      .ok ⟨{next with alias := aliasStep next.alias (a, record.input.base.nextVreg)},
        next.base.emitted, [[.vreg record.input.base.nextVreg .int]], trace⟩ := by
    unfold emitInstruction
    rw [infoBang, rootRun]
    simp only [bind, Except.bind]
    simp [results, installed]
  obtain ⟨actual, actualRun, actualScan⟩ := stock_emitted_scan (record_execute run events records) recorded emitted
  have same := Except.ok.inj (actualRun.symm.trans emitter)
  subst actual
  rw [actualScan] at recorded
  have stepEq := Option.some.inj recorded.symm
  refine ⟨nx, ny, mx, my, ?_, ?_, ?_, ?_⟩
  · rw [stepEq]
  · rw [actualScan, nextEq]
    change ((scanState record.input record.inst).base.fresh .int).2.emitted.push _ = _
    simp [LState.fresh, scan_empty, scan_frontier]
  · rw [actualScan, nextEq]
    change ((scanState record.input record.inst).base.fresh .int).2.nextVreg = _
    simp only [LState.fresh, scan_frontier]
  · rw [actualScan, nextEq]
    change (((scanState record.input record.inst).mark x).mark y).demand = _
    simp only [State.mark, scanState_demands]

/-- The actual selected record's code establishes the binary result and
preserves every other demanded, source-available value. No emitted-code,
machine-execution, definition-bound or final-result-alias certificate is supplied. -/
theorem stock_lower_alu_available_values {f : Clif.Function} {result : Result}
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
    (operands : ValuesHeld (fun v => v = x ∨ v = y) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
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
  obtain ⟨nx, ny, mx, my, outputs, code, upper, demands⟩ :=
    stock_lower_alu_record_shape run scope events records subtract width source results mapped recorded emitted evalRun rootRun
  have bound : result.final.alias.size ≤ record.input.base.nextVreg := by
    simpa only [scan_frontier] using stock_lower_blockScanAliasBounds run event events record records
  have operation : ((if subtract then ALUOp.sub else .add), (if subtract then Clif.BinaryOp.isub else .iadd)) =
      (.add, .iadd) ∨ ((if subtract then ALUOp.sub else .add), (if subtract then Clif.BinaryOp.isub else .iadd)) =
      (.sub, .isub) ∨ ((if subtract then ALUOp.sub else .add), (if subtract then Clif.BinaryOp.isub else .iadd)) =
      (.and, .band) ∨ ((if subtract then ALUOp.sub else .add), (if subtract then Clif.BinaryOp.isub else .iadd)) =
      (.orr, .bor) ∨ ((if subtract then ALUOp.sub else .add), (if subtract then Clif.BinaryOp.isub else .iadd)) =
      (.eor, .bxor) := by cases subtract <;> simp
  obtain ⟨ρ', executed, value, kept⟩ := stock_alu_rrr_resolved refines operation width bound mx my operands sourceX sourceY
  have actualCode : record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1))) =
      [(MInst.aluRRR (if subtract then .sub else .add) (szOf ty.width)
        (.vreg record.input.base.nextVreg .int) (.vreg nx .int) (.vreg ny .int)).mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1))] := by rw [code]; rfl
  have actualExecution : PRun F isem (record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' := by
    rw [actualCode]; exact executed
  have terminal : aliasNum result.final.alias record.input.base.nextVreg = record.input.base.nextVreg := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bound]
    rfl
  have defs : ∀ m ∈ record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1))), ∀ key ∈ vdefs m,
        record.input.base.nextVreg ≤ key ∧ key < record.output.state.base.nextVreg := by
    rw [actualCode]
    intro m member key defined
    have equal := List.mem_singleton.mp member
    subst m
    simp only [MInst.mapRegs, resolve_vreg] at defined
    change key ∈ [aliasNum result.final.alias record.input.base.nextVreg] at defined
    rw [terminal] at defined
    have equal := List.mem_singleton.mp defined
    subst key
    rw [upper]
    omega
  obtain ⟨w', execution, _⟩ := actualExecution Arm.ArmState.default
  have transferred := stock_lower_fresh_record_values_auto_demand run scope dominated events records
    block statement current source clif results statementResults mapped recorded emitted outputs
    (Nat.le_refl _) held defs execution value
  exact ⟨ρ', actualExecution, value, kept, transferred⟩

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
theorem stock_lower_alu_available_values_witness (subtract : Bool) :
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
    obtain ⟨ρ', executed, value, kept, installed⟩ := stock_lower_alu_available_values run
      (exampleScope subtract) (exampleDominated subtract) events records
      (bi := 0) (j := 0) (b := (exampleFunction subtract).blocks[0]!)
      (stm := ⟨[100], .binary (if subtract then .isub else .iadd) .i64 7 31⟩)
      rfl rfl (by simpa only [blockStart, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add] using current)
      subtract (by decide) source' clif results rfl mapped recorded emitted
      (n := 0) evalRun rootRun self operandHeld held sourceX sourceY
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
