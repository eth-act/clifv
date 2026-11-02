import FV.Backend.Proof.StockReturnHelpers
import FV.Backend.Proof.StockReturnRootCalls
import FV.Backend.Proof.StockTermDataOrigin

/-! Connect return helper execution to actual retained records, including the
empty result binder and complete state/code. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- The real named return call supplies its own selected root and helper. -/
theorem stock_named_return_helper {ctx : Ctx} {i : Nat} {xs : List Nat}
    (slot : ctx.insts[i]? = some ⟨.data 152 18 [.data 151 7 [],.values xs],[],[],none⟩)
    {st next : State} {out : V} {rules : List RuleId}
    (run : Stock.runTerm ctx "lower" [.inst i] st = .ok (some out,next,rules)) :
    rules.getLast? = some rule_lower_2574.id ∧
      ∃ fuel trace,60 ≤ fuel ∧ ApplyInternal program (Stock.sem ctx) {} fuel 25 294 [.values xs]
        (st,#[]) out (next,trace) := by
  obtain ⟨selected⟩ := stock_named_lower_selection run
  obtain ⟨chosen,_,_,_,fuel,enough,helper⟩ := stock_return_selected_calls slot selected
  exact ⟨by rw [selected.last_rule,chosen],fuel,selected.rhsTrace,enough,helper⟩

/-- Whole-driver original return records derive the real helper, the exact
empty result binder, mapped requests, ABI pins and complete emitted code. -/
theorem stock_lower_return_record_helper {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {xs : List Nat} (ret : b.term = .ret xs)
    {record : ScanRecord} (records : record ∈ event.output.records)
    (terminal : record.inst = event.termInst)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ fuel trace rs ps,60 ≤ fuel ∧
      ApplyInternal program (Stock.sem event.ctx) {} fuel 25 294 [.values (xs ++ sretRet f)]
        (scanState record.input record.inst,#[]) (.regsVec []) (record.output.state,trace) ∧
      step.rules.getLast? = some rule_lower_2574.id ∧
      (xs ++ sretRet f).mapM event.ctx.valueReg? = some rs ∧ returnPins f rs.length = some ps ∧
      record.output.state = {(xs ++ sretRet f).foldl State.mark (scanState record.input record.inst) with
        base := ((xs ++ sretRet f).foldl State.mark (scanState record.input record.inst)).base.emit (.rets (rs.zip ps))} ∧
      record.output.emitted = #[.rets (rs.zip ps)] := by
  obtain ⟨original,data,found,prepared,slot⟩ := stock_lower_blockScan_term_data run scope events
  have same := Option.some.inj (found.symm.trans block)
  subst original
  rw [ret] at prepared
  change Backend.termData (.ret (xs ++ sretRet f)) = .ok data at prepared
  rw [termData_ret] at prepared
  cases prepared
  rw [← terminal] at slot
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  obtain ⟨chosen,_,_,_,fuel,enough,helper⟩ := stock_return_selected_calls slot receipt.selected
  obtain ⟨rs,ps,safe,mapped,pinned,state,output⟩ := stock_lower_return_observed data_program rfl enough helper
  have binding := receipt.binding
  simp only [getElem!_def,slot,Option.getD_some,List.zip_nil_left] at binding
  change Except.ok (receipt.next,#[]) = Except.ok (receipt.bound,receipt.copies) at binding
  obtain ⟨boundEq,copiesEq⟩ := Prod.mk.inj (Except.ok.inj binding)
  have actualState : record.output.state = receipt.next := receipt.state.trans boundEq.symm
  have empty : (scanState record.input record.inst).base.emitted = #[] := by
    unfold scanState; dsimp only; split <;> rfl
  have marked : ∀ ys : List Nat,(ys.foldl State.mark (scanState record.input record.inst)).base.emitted = #[] := by
    intro ys
    have keep : ∀ (ys : List Nat) (st : State),(ys.foldl State.mark st).base = st.base := by
      intro ys st
      induction ys generalizing st with
      | nil => rfl
      | cons y ys ih => exact ih (st.mark y)
    rw [keep]; exact empty
  have pinSource := (stock_lower_record_context run scope events).1.func
  rw [pinSource] at pinned
  refine ⟨fuel,receipt.selected.rhsTrace,rs,ps,enough,?_,?_,mapped,pinned,actualState.trans state,?_⟩
  · rw [actualState,← output]; exact helper
  · rw [receipt.rules,receipt.selected.last_rule,chosen]
  · rw [receipt.code,← boundEq,← copiesEq,state]
    simp only [LState.emit,marked,Array.append_empty]
    rfl
end Backend.Stock.Proof
