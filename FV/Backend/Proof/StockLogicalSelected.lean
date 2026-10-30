import FV.Backend.Proof.IselCtlRuleIds
import FV.Backend.Proof.StockConstantRecordValues
import FV.Backend.Proof.StockSelectionReceipts

/-! Typed logical-root receipts derived from actual Stock record selection. -/
namespace Backend.Stock.Proof.LogicalSelected
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

inductive Kind where
  | band | bor | bxor

def Kind.cop : Kind → Clif.BinaryOp
  | .band => .band | .bor => .bor | .bxor => .bxor

def Kind.rule : Kind → Rule
  | .band => rule_lower_1412 | .bor => rule_lower_1449 | .bxor => rule_lower_1516

private def Kind.opcode : Kind → Nat
  | .band => 97 | .bor => 98 | .bxor => 99

private theorem root_member (kind : Kind) : kind.rule ∈ program.rulesOf T.lower.id := by
  cases kind <;> rw [show T.lower.id = 686 from rfl, data_program.r686] <;> decide +kernel

private theorem stock_sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem stock_sem_unData (ctx : Ctx) (ty t k : Nat) (fs : List V) :
    (Stock.sem ctx).unData ty (.data t k fs) = if t = ty then some (k, fs) else none :=
  sem_unData ctx ty t k fs

/-- Matching a logical Stock root retains the complete scheduling state. -/
theorem stock_match_logical {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (kind : Kind) {i x y w : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w)) (width : w ≤ 64)
    (data : info.data = .data 152 2 [.data 151 kind.opcode [], .values [x,y]])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) cfg (n + 2) kind.rule [.inst i]).run (st,tr) =
      .ok (some (env3 (.ty (.int w)) (.value x) (.value y)),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have fits := ext_fits_in_64 ctx st.base w
  simp only [width, ↓reduceIte] at fits
  cases hp
  cases kind <;> isel_eval [*, Kind.rule, Kind.opcode, rule_lower_1412, rule_lower_1449,
    rule_lower_1516, stock_sem_extract, stock_sem_unData, ext_ty_int, ext_value_array_2]

section ContextData
attribute [local semireducible] Isle.Aarch64.program
private theorem logical_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (kind : Kind) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y)) :
    ty.width ≤ 64 ∧ info.data = .data 152 2 [.data 151 kind.opcode [], .values [x,y]] ∧
      info.resTys.head? = some (.int ty.width) := by
  have supported := inv.instE i info _ source clif
  have he : eTy ty = true := by
    cases kind <;> simpa [Kind.cop,Compile.instE,Compile.binaryE,Compile.tyE,eTy] using supported
  have data := inv.data i info _ source clif
  obtain ⟨types,result,typed,len⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨eTy_width he, ?_, ?_⟩
  · have shape : instData f (.binary kind.cop ty x y) =
        .ok (.data 152 2 [.data 151 kind.opcode [], .values [x,y]]) := by
      cases kind <;> simp only [Kind.cop,Kind.opcode,instData,binaryOpcode,he,ite_true] <;> rfl
    exact Except.ok.inj (data.symm.trans shape)
  · rw [typed]; simp [ofClif_int_width (isInt_of_eTy he)]
end ContextData

/-- Actual source facts and the final selected root ID determine the typed RHS
receipt. No caller-supplied width, match environment or RHS execution is needed. -/
theorem stock_lower_logical_selected_receipts {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (kind : Kind) {info : IInfo} {x y : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some kind.rule.id) :
    ty.width ≤ 64 ∧ ∃ (out : V) (next : State) (trace : List RuleId) (rhsTrace : Array RuleId),
      Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) = .ok (some out,next,trace) ∧
      (evalExpr program (Stock.sem event.ctx) {} 999999 kind.rule.rhs
        (env3 (.ty (.int ty.width)) (.value x) (.value y))).run
          (scanState record.input record.inst,#[]) = .ok (some out,next,rhsTrace) := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have last : receipt.fired.getLast? = some kind.rule.id := by
    rw [← receipt.rules]; exact selectedId
  have idEq := Option.some.inj (receipt.selected.last_rule.symm.trans last)
  have ruleEq := eq_of_mem_of_id lower_ids_nodup receipt.selected.rule_mem (root_member kind) idEq
  obtain ⟨width,data,type⟩ := logical_data (stock_lower_record_context run scope events).1 kind source clif
  have fuelBound := receipt.selected.fuelBound
  have count : (program.rulesOf T.lower.id).length ≤ 999995 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
  have enough : 2 ≤ receipt.selected.matchFuel := by omega
  obtain ⟨n,fuelEq⟩ : ∃ n, receipt.selected.matchFuel = n + 2 := ⟨receipt.selected.matchFuel - 2,by omega⟩
  have actualMatch := receipt.selected.matchedRun
  rw [ruleEq,fuelEq] at actualMatch
  have expected := stock_match_logical data_program event.ctx (cfg := {}) kind source type width data
    (scanState record.input record.inst) #[] n
  have same := Except.ok.inj (actualMatch.symm.trans expected)
  have envEq := Option.some.inj (congrArg Prod.fst same)
  have stateEq := congrArg (fun q => q.2.1) same
  have traceEq := congrArg (fun q => q.2.2) same
  change receipt.selected.matched = scanState record.input record.inst at stateEq
  change receipt.selected.matchTrace = #[] at traceEq
  have evaluated := receipt.selected.rhsRun
  rw [ruleEq,envEq,stateEq,traceEq] at evaluated
  exact ⟨width,receipt.out,receipt.next,receipt.fired,receipt.selected.rhsTrace,receipt.rootRun,evaluated⟩

section Witness
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private def exampleFunction (kind : Kind) : Clif.Function := {
  name := "selected_logical_record"
  sig := { params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩], callConv := some .systemV }
  blocks := [{id := 0,params := [(7,.i64),(31,.i64)],body := [⟨[100],.binary kind.cop .i64 7 31⟩],term := .ret [100]}] }
private theorem exampleScope (kind : Kind) : LowerScope (exampleFunction kind) :=
  lowerScope_of (by cases kind <;> decide +kernel)

private theorem observed (kind : Kind) :
    (Stock.lower (exampleFunction kind)).toOption.map (fun result =>
      result.blockScans.toList.any (fun event => event.output.records.any (fun record =>
        record.inst == 0 &&
        decide ((event.ctx.insts[0]?).map (fun info => info.clif) = some (some (.binary kind.cop .i64 7 31))) &&
        record.output.step.any (fun step => step.decision == .emitted &&
          decide (step.rules.getLast? = some kind.rule.id))))) = some true := by
  cases kind <;> decide +kernel

/-- Complete sparse-ID AND/OR/XOR runs inhabit actual selected records and their
source-derived typed match/RHS receipts, rather than assuming helper selection. -/
theorem stock_logical_selected_witness (kind : Kind) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (info : IInfo) (step : Step),
      Stock.lower (exampleFunction kind) = .ok result ∧ LowerScope (exampleFunction kind) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.binary kind.cop .i64 7 31) ∧
      record.output.step = some step ∧ step.decision = .emitted ∧ step.rules.getLast? = some kind.rule.id ∧
      ∃ (out : V) (next : State) (trace : List RuleId) (rhsTrace : Array RuleId),
        Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) = .ok (some out,next,trace) ∧
        (evalExpr program (Stock.sem event.ctx) {} 999999 kind.rule.rhs
          (env3 (.ty (.int 64)) (.value 7) (.value 31))).run
            (scanState record.input record.inst,#[]) = .ok (some out,next,rhsTrace) := by
  have actual := observed kind
  cases run : Stock.lower (exampleFunction kind) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    have successful : (Stock.lower (exampleFunction kind)).toOption = some result := by rw [run]; rfl
    rw [successful,Option.map_some,Option.some.injEq] at actual
    obtain ⟨event,events,record,records,current,sourceData,stepData⟩ := (by
      simpa only [List.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,and_assoc] using actual :
        ∃ event ∈ result.blockScans.toList, ∃ record ∈ event.output.records,
          record.inst = 0 ∧
          (event.ctx.insts[0]?).map (fun info => info.clif) = some (some (.binary kind.cop .i64 7 31)) ∧
          record.output.step.any (fun step => step.decision == .emitted &&
            decide (step.rules.getLast? = some kind.rule.id)) = true)
    obtain ⟨info,source,clif⟩ := (by simpa only [Option.map_eq_some_iff] using sourceData :
      ∃ info, event.ctx.insts[0]? = some info ∧ info.clif = some (.binary kind.cop .i64 7 31))
    rw [← current] at source
    obtain ⟨step,recorded,emitted,selectedId⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧ step.rules.getLast? = some kind.rule.id)
    obtain ⟨width,out,next,trace,rhsTrace,rootRun,rhsRun⟩ := stock_lower_logical_selected_receipts run
      (exampleScope kind) events records kind source clif recorded emitted selectedId
    exact ⟨result,event,record,info,step,rfl,exampleScope kind,events,records,source,clif,recorded,emitted,
      selectedId,out,next,trace,rhsTrace,rootRun,rhsRun⟩
end Witness
end Backend.Stock.Proof.LogicalSelected
