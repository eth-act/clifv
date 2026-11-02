import FV.Backend.Proof.StockSourceView
import FV.Backend.Proof.StockPatternSource
import FV.Backend.Proof.StockSelectionReceipts
import FV.Backend.Proof.IselExcl
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
/-- The existing checked exclusion table applies to actual Stock source
patterns through the mapped source view. Scheduling state and register numbers
supply no additional accepted-input condition. -/
theorem stock_excluded_root_args {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {r : Rule} (member : r ∈ program.rulesOf TId.lower) (excluded : closureRoot r = false)
    {i : Nat} {info : IInfo} {inst : Clif.Inst} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some inst) (st : State) (env bound : Isle.Interp.Env V) :
    matchArgs program (Stock.sem ctx) st r.args [.inst i] env ≠ .ok (some bound) := by
  intro matched
  have checked := List.all_eq_true.mp exclOk_program r member
  rw [closureRoot_eq] at excluded
  simp only [exclOk,excluded,Bool.false_or] at checked
  have view : DFGViewEq ctx (sourceIdentityCtx ctx) := ⟨rfl,rfl,rfl,rfl,rfl⟩
  rw [stock_matchArgs_source view] at matched
  split at checked
  · rename_i q argsEq
    rw [argsEq] at matched
    obtain ⟨middle,head,tail⟩ := matchArgs_cons_inv matched
    exact fails_sound mapped.identityView q .inst _ _ _ _ checked
      ⟨i,info,inst,rfl,source,clif,mapped.data i info inst source clif⟩ head
  · cases checked
/-- A generated lower root excluded by the original closure cannot be selected
by the actual Stock matcher, independently of its if-let constructor behavior. -/
theorem stock_excluded_root_match {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {r : Rule} (member : r ∈ program.rulesOf TId.lower) (excluded : closureRoot r = false)
    {i : Nat} {info : IInfo} {inst : Clif.Inst} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some inst) (cfg : Config) (fuel : Nat) (st next : State × Array RuleId)
    (env : Isle.Interp.Env V) :
    (matchRule program (Stock.sem ctx) cfg fuel r [.inst i]).run st ≠ .ok (some env,next) := by
  intro matched
  cases fuel with
  | zero => rw [matchRule.eq_1] at matched; cases matched
  | succ fuel =>
    obtain ⟨bound,args,rest⟩ := matchRule_some_inv matched
    exact stock_excluded_root_args mapped member excluded source clif st.1 _ bound args
/-- Real first-match selection derives membership in the original closure
internally; a caller does not supply a reachable-rule certificate. -/
theorem stock_selected_source_root_closure {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {i : Nat} {info : IInfo} {inst : Clif.Inst} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some inst) {before after : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i before out after trace) : closureRoot selected.rule = true := by
  cases closed : closureRoot selected.rule with
  | false => exact False.elim (stock_excluded_root_match mapped selected.rule_mem closed source clif {} selected.matchFuel
      (before,#[]) (selected.matched,selected.matchTrace) selected.env selected.matchedRun)
  | true => rfl
/-- Every actual emitted ordinary source record carries a closure root, using
only the unchanged source scope and the real retained selection. Terminator and
branch obligations remain separate. -/
theorem stock_lower_source_record_closure {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {inst : Clif.Inst} (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some inst) {step : Step} (recorded : record.output.step = some step)
    (emitted : step.decision = .emitted) :
    Nonempty (RecordSelection event record step) ∧ step.rules.getLast?.any (closureRootIds.contains) = true := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have closed := stock_selected_source_root_closure (stock_lower_record_context run scope events).1 source clif receipt.selected
  refine ⟨⟨receipt⟩,?_⟩
  rw [receipt.rules,receipt.selected.last_rule]
  simpa only [Option.any_some,closureRoot_eq] using closed
end Backend.Stock.Proof
