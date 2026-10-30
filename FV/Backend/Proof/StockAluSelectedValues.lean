import FV.Backend.Proof.StockAluOperandCoverage
import FV.Backend.Proof.StockSelectionReceipts
import FV.Backend.Proof.IselCtl

/-! Add/subtract typed receipts derived from actual record selection. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem alu_member (subtract : Bool) :
    (if subtract then rule_lower_801 else rule_lower_86) ∈ program.rulesOf T.lower.id := by
  cases subtract <;> rw [show T.lower.id = 686 from rfl, data_program.r686] <;> decide +kernel

section AluData
attribute [local semireducible] Isle.Aarch64.program

private theorem alu_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x y : Nat} {info : IInfo} {ty : Clif.Ty} (subtract : Bool)
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y)) :
    ty.width ≤ 64 ∧ info.data = .data 152 2 [.data 151 (if subtract then 74 else 73) [], .values [x,y]] ∧
      info.resTys.head? = some (.int ty.width) := by
  have supported := inv.instE i info _ source clif
  have he : eTy ty = true := by
    cases subtract <;> simpa [Compile.instE, Compile.binaryE, Compile.tyE, eTy] using supported
  have data := inv.data i info _ source clif
  obtain ⟨types, result, typed, len⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨eTy_width he, ?_, ?_⟩
  · have shape : instData f (.binary (if subtract then .isub else .iadd) ty x y) =
        .ok (.data 152 2 [.data 151 (if subtract then 74 else 73) [], .values [x,y]]) := by
      cases subtract
      · simp only [Bool.false_eq_true, ite_false, instData, show binaryOpcode .iadd = some "Iadd" from rfl, he, ite_true]
        rfl
      · simp only [ite_true, instData, show binaryOpcode .isub = some "Isub" from rfl, he]
        rfl
    exact Except.ok.inj (data.symm.trans shape)
  · rw [typed]; simp [ofClif_int_width (isInt_of_eTy he)]

end AluData

/-- The actual final root ID determines the chosen add/subtract rule. Source
facts and its actual match then supply the typed environment and unchanged state. -/
theorem stock_lower_alu_selected_receipts {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {x y : Nat} {ty : Clif.Ty} (subtract : Bool)
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (if subtract then rule_lower_801 else rule_lower_86).id) :
    ty.width ≤ 64 ∧ ∃ (out : V) (next : State) (trace : List RuleId) (rhsTrace : Array RuleId),
      Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) = .ok (some out,next,trace) ∧
      (evalExpr program (Stock.sem event.ctx) {} 999999
        (if subtract then rule_lower_801 else rule_lower_86).rhs
        (env3 (.ty (.int ty.width)) (.value x) (.value y))).run
          (scanState record.input record.inst, #[]) = .ok (some out, next, rhsTrace) := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have last : receipt.fired.getLast? = some (if subtract then rule_lower_801 else rule_lower_86).id := by
    rw [← receipt.rules]; exact selectedId
  have idEq := Option.some.inj (receipt.selected.last_rule.symm.trans last)
  have ruleEq := eq_of_mem_of_id lower_ids_nodup receipt.selected.rule_mem (alu_member subtract) idEq
  obtain ⟨width, data, type⟩ := alu_data (stock_lower_record_context run scope events).1 subtract source clif
  have fuelBound := receipt.selected.fuelBound
  have count : (program.rulesOf T.lower.id).length ≤ 999995 := by
    rw [show T.lower.id = 686 from rfl, data_program.r686]; decide +kernel
  have enough : 2 ≤ receipt.selected.matchFuel := by omega
  obtain ⟨n, fuelEq⟩ : ∃ n, receipt.selected.matchFuel = n + 2 := ⟨receipt.selected.matchFuel - 2, by omega⟩
  have actualMatch := receipt.selected.matchedRun
  rw [ruleEq, fuelEq] at actualMatch
  have expected : (matchRule program (Stock.sem event.ctx) {} (n + 2)
      (if subtract then rule_lower_801 else rule_lower_86) [.inst record.inst]).run
        (scanState record.input record.inst, #[]) =
      .ok (some (env3 (.ty (.int ty.width)) (.value x) (.value y)), scanState record.input record.inst, #[]) := by
    cases subtract
    · exact stock_match_86 data_program event.ctx source type width data _ #[] n
    · exact stock_match_801 data_program event.ctx source type width data _ #[] n
  have same := Except.ok.inj (actualMatch.symm.trans expected)
  have envEq := Option.some.inj (congrArg Prod.fst same)
  have stateEq := congrArg (fun q => q.2.1) same
  have traceEq := congrArg (fun q => q.2.2) same
  change receipt.selected.matched = scanState record.input record.inst at stateEq
  change receipt.selected.matchTrace = #[] at traceEq
  have evaluated := receipt.selected.rhsRun
  rw [ruleEq, envEq, stateEq, traceEq] at evaluated
  exact ⟨width, receipt.out, receipt.next, receipt.fired, receipt.selected.rhsTrace, receipt.rootRun, evaluated⟩

/-- Classifying an actual emitted record by its final rule ID derives all
match/RHS/root receipts and operand coverage internally before value transfer. -/
theorem stock_lower_alu_selected_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {z a x y : Nat} {ty : Clif.Ty} (subtract : Bool)
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (if subtract then rule_lower_801 else rule_lower_86).id)
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
  obtain ⟨width, out, next, trace, rhsTrace, rootRun, evalRun⟩ := stock_lower_alu_selected_receipts
    run scope events records subtract source clif recorded emitted selectedId
  exact stock_lower_alu_available_values_auto_operands run scope dominated events records block statement current
    subtract width source clif results statementResults mapped recorded emitted (n := 999959) evalRun rootRun
    refines held sourceX sourceY

attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
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
          record.output.step.any (fun step => step.decision == .emitted &&
            decide (step.rules.getLast? = some (if subtract then rule_lower_801 else rule_lower_86).id)) &&
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
theorem stock_lower_alu_selected_values_witness (subtract : Bool) :
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
          record.output.step.any (fun step => step.decision == .emitted &&
            decide (step.rules.getLast? = some (if subtract then rule_lower_801 else rule_lower_86).id)) = true ∧
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
    obtain ⟨step, recorded, emitted, selectedId⟩ := (by
      simpa only [Option.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using stepData :
        ∃ step, record.output.step = some step ∧ step.decision = .emitted ∧
          step.rules.getLast? = some (if subtract then rule_lower_801 else rule_lower_86).id)
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
    obtain ⟨ρ', executed, value, kept, installed⟩ := stock_lower_alu_selected_values run
      (exampleScope subtract) (exampleDominated subtract) events records
      (bi := 0) (j := 0) (b := (exampleFunction subtract).blocks[0]!)
      (stm := ⟨[100], .binary (if subtract then .isub else .iadd) .i64 7 31⟩)
      rfl rfl (by simpa only [blockStart, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add] using current)
      subtract source' clif results rfl mapped recorded emitted
      selectedId self held sourceX sourceY
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
