module

public import FV.Backend.Proof.StockScopeRoots
public import FV.Backend.Proof.LowerDecide

@[expose] public section

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def scopeFunction : Clif.Function := {
  name := "stock_scope_roots"
  sig := {returns := [⟨.i8,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [],body := [⟨[2],.iconst .i8 7⟩],term := .ret [2]}] }
private def scopeBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx scopeFunction).toOption.getD (sinkCtx,#[],sinkState)
private theorem scope_build : Stock.buildCtx scopeFunction = .ok scopeBuilt := rfl
private theorem scope_condition : LowerScope scopeFunction := lowerScope_of (by decide +kernel)
private theorem scope_source : scopeBuilt.1.insts[0]? = some scopeBuilt.1.insts[0]! := rfl
private theorem scope_clif : scopeBuilt.1.insts[0]!.clif = some (.iconst .i8 7) := rfl
private theorem excluded_member : rule_lower_58 ∈ program.rulesOf TId.lower := by
  rw [show TId.lower = 686 from rfl,data_program.r686]; decide +kernel
private theorem excluded_closed : closureRoot rule_lower_58 = false := by
  rw [closureRoot_eq]; decide +kernel
section Runs
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed : (Stock.lower scopeFunction).toOption.map (fun result =>
    result.blockScans.toList.any (fun event => event.output.records.any (fun record =>
      record.inst == 0 && decide ((event.ctx.insts[record.inst]?).map (fun info => (info.clif,info.results)) =
        some (some (.iconst .i8 7),[2])) &&
      record.output.step.any (fun step => step.decision == .emitted)))) = some true := by decide +kernel
end Runs
/-- A real nonempty mapped context and a concrete excluded floating root
inhabit all pattern/matcher exclusion premises, including nonempty source IDs. -/
theorem stock_excluded_source_roots_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (st : State) (info : IInfo) (r : Rule),
      LowerScope f ∧ Stock.buildCtx f = .ok (ctx,ranges,st) ∧ MappedCtxInv f ctx ∧
      ctx.insts[0]? = some info ∧ info.clif = some (.iconst .i8 7) ∧
      ctx.valueReg? 2 = some (.vreg 192 .int) ∧ r ∈ program.rulesOf TId.lower ∧ closureRoot r = false ∧
      (∀ env bound,matchArgs program (Stock.sem ctx) st r.args [.inst 0] env ≠ .ok (some bound)) ∧
      (∀ cfg fuel env next,(matchRule program (Stock.sem ctx) cfg fuel r [.inst 0]).run (st,#[]) ≠ .ok (some env,next)) := by
  have mapped := buildCtx_mappedInv scope_condition scope_build
  refine ⟨scopeFunction,scopeBuilt.1,scopeBuilt.2.1,scopeBuilt.2.2,scopeBuilt.1.insts[0]!,rule_lower_58,
    scope_condition,scope_build,mapped,scope_source,scope_clif,rfl,excluded_member,excluded_closed,?_,?_⟩
  · intro env bound
    exact stock_excluded_root_args mapped excluded_member excluded_closed scope_source scope_clif _ env bound
  · intro cfg fuel env next
    exact stock_excluded_root_match mapped excluded_member excluded_closed scope_source scope_clif cfg fuel _ next env
/-- An actual emitted constant source record supplies both complete selection
and closure membership under the original scope. It does not merely assume a
rule is reachable or replay/checker acceptance. -/
theorem stock_selected_source_closure_witness :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step) (info : IInfo)
      (receipt : RecordSelection event record step),
      Stock.lower scopeFunction = .ok result ∧ LowerScope scopeFunction ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.iconst .i8 7) ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      closureRoot receipt.selected.rule = true ∧ step.rules.getLast?.any (closureRootIds.contains) = true := by
  have actual := observed
  cases run : Stock.lower scopeFunction with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    simp only [run,Except.toOption,Option.map_some,Option.some.injEq,List.any_eq_true,Bool.and_eq_true,
      beq_iff_eq,decide_eq_true_eq,and_assoc] at actual
    obtain ⟨event,events,record,records,current,key,stepData⟩ := actual
    obtain ⟨info,source,same⟩ := Option.map_eq_some_iff.mp key
    have clif := congrArg Prod.fst same
    change info.clif = some (.iconst .i8 7) at clif
    obtain ⟨step,recorded,emitted⟩ := (by
      simpa only [Option.any_eq_true,beq_iff_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted)
    obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
    have closed := stock_selected_source_root_closure (stock_lower_record_context run scope_condition events).1
      source clif receipt.selected
    have final := (stock_lower_source_record_closure run scope_condition events records source clif recorded emitted).2
    exact ⟨result,event,record,step,info,receipt,rfl,scope_condition,events,records,source,clif,recorded,emitted,closed,final⟩
end Backend.Stock.Proof
