import FV.Backend.Proof.StockAcquireFrozenSourceFrame

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem setAlias_base {st next : State} {dst src : Reg}
    (h : st.setAlias dst src = .ok next) : next.base = st.base := by
  cases dst <;> cases src <;>
    simp only [State.setAlias,bind,Except.bind,pure,Except.pure,throw,throwThe,MonadExceptOf.throw] at h
  all_goals repeat' first | (solve | cases h; rfl) | (solve | cases h) | split at h
private theorem fold_base {α β : Type} (field : α → LState)
    (step : α → β → Except String α)
    (preserves : ∀ a b next,step a b = .ok next → field next = field a)
    (xs : List β) {a next : α} (run : xs.foldlM step a = .ok next) : field next = field a := by
  induction xs generalizing a with
  | nil => cases run; rfl
  | cons x xs ih =>
    rw [List.foldlM_cons] at run
    cases call : step a x with
    | error e => simp only [call,bind,Except.bind] at run; cases run
    | ok middle => simp only [call,bind,Except.bind] at run; exact (ih run).trans (preserves _ _ _ call)
theorem acquire_bind_results_base {ctx : Ctx} {pairs : List (Nat × List Reg)} {st next : State} {copies : Array MInst}
    (run : bindResults ctx pairs st = .ok (next,copies)) : next.base = st.base := by
  unfold bindResults at run
  apply fold_base (fun a : State × Array MInst => a.1.base) _ ?_ pairs run
  intro acc pair next call
  rcases acc with ⟨s,code⟩
  rcases pair with ⟨v,rs⟩
  dsimp only at call
  cases mapped : ctx.valueReg? v with
  | none => simp only [mapped] at call; cases call
  | some r =>
    simp only [mapped] at call
    split at call
    · rename_i _ n cls
      cases alias : s.setAlias r (.vreg n cls) with
      | error e => simp only [alias,bind,Except.bind] at call; cases call
      | ok q => simp only [alias,bind,Except.bind,pure,Except.pure] at call; cases call; exact setAlias_base alias
    · cases call; rfl
    · cases call

/-- The real final rule ID selects the fallback extension case internally. -/
theorem fallback_extend_selected_rule {ctx : Ctx} {i : Nat} {st next : State} {out : V} {rules : List RuleId}
    (signed : Bool) (selected : LowerSelection ctx i st out next rules)
    (last : rules.getLast? = some (ScalarCast.extendRule signed).id) :
    selected.rule = ScalarCast.extendRule signed := by
  have idEq := Option.some.inj (selected.last_rule.symm.trans last)
  have candidate : ScalarCast.extendRule signed ∈ program.rulesOf T.lower.id := by
    cases signed <;> rw [ScalarCast.extendRule,show T.lower.id = 686 from rfl,data_program.r686] <;> decide +kernel
  exact eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate idEq

/-- Actual fallback emission allocates exactly one register, independently of later source execution. -/
theorem stock_lower_fallback_extend_frontier_step {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (signed : Bool) {info : IInfo} {target : Clif.Ty} {x : Nat}
    (installed : event.ctx.insts[record.inst]? = some info)
    (source : info.clif = some (.extend (ScalarCast.extendOp signed) target x))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (ScalarCast.extendRule signed).id) :
    record.output.state.base.nextVreg = record.input.base.nextVreg+1 := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have last : receipt.fired.getLast? = some (ScalarCast.extendRule signed).id := by rw [← receipt.rules];exact selectedId
  have chosen := fallback_extend_selected_rule signed receipt.selected last
  obtain ⟨sourceType,pointer,typed,accepted,mapped,output,nextEq⟩ := fallback_extend_selected_shape
    (stock_lower_record_context run scope events).1 signed installed source receipt.selected chosen
  rw [receipt.state,acquire_bind_results_base receipt.binding,nextEq]
  simp only [State.mark,LState.fresh,LState.emit,scanState]
  split <;> rfl

/-- Final aliases retain the actual fallback fragment's fresh definition interval. -/
theorem stock_lower_fallback_extend_resolved_defs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (signed : Bool) {info : IInfo} {target : Clif.Ty} {x : Nat}
    (installed : event.ctx.insts[record.inst]? = some info)
    (source : info.clif = some (.extend (ScalarCast.extendOp signed) target x))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (ScalarCast.extendRule signed).id) :
    ∀ instruction ∈ record.output.emitted.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))),
      ∀ key ∈ vdefs instruction,record.input.base.nextVreg ≤ key ∧ key < record.output.state.base.nextVreg := by
  obtain ⟨sourceType,pointer,resultId,key,dest,typed,accepted,mapped,results,resultMap,fresh,output,chunk⟩ :=
    stock_lower_fallback_extend_record run scope dominated events records signed installed source recorded emitted selectedId
  have terminal := (stock_lower_freshAlias_terminal run (n := dest) (by
    rw [fresh]
    exact stock_lower_blockScanInitialFrontier run event events record records)).2
  have upper := stock_lower_fallback_extend_frontier_step run scope events records signed installed source recorded emitted selectedId
  intro instruction member defined defMember
  rw [chunk] at member
  change instruction ∈ [(MInst.extend (.vreg dest .int) (.vreg pointer .int) signed sourceType.bits target.width).mapRegs
    (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))] at member
  have same := List.mem_singleton.mp member
  subst instruction
  change defined ∈ vdefs (.extend
    (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg dest .int))
    (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg pointer .int)) signed sourceType.bits target.width) at defMember
  rw [resolve_vreg,resolve_vreg] at defMember
  change defined ∈ vdefs (.extend (.vreg (aliasNum result.final.alias dest) .int)
    (.vreg (aliasNum result.final.alias pointer) .int) signed sourceType.bits target.width) at defMember
  rw [terminal,vdefs_extend'] at defMember
  have same := List.mem_singleton.mp defMember
  subst defined
  rw [fresh,upper]
  exact ⟨Nat.le_refl _,by omega⟩

end Backend.Stock.Proof.Acquire810
