import FV.Backend.Proof.StockAcquirePendingFreshValues

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

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
private theorem binding_base {ctx : Ctx} {pairs : List (Nat × List Reg)} {st next : State} {copies : Array MInst}
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

/-- The actual selected acquire allocates precisely its one fresh result register. -/
theorem stock_lower_acquire_record_frontier_step {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    record.output.state.base.nextVreg = record.input.base.nextVreg+1 := by
  obtain ⟨R,middle,requested,address,next,bound,copies,sink,request,register,marked,state,root,binding,final,code⟩ :=
    stock_lower_acquire_selected_emission run scope dominated events records recorded emitted selectedId
  rw [final,binding_base binding,state,marked,(sink_accepted sink).2.2.2.2]
  simp only [State.mark,LState.emit,LState.fresh,scanState]
  split <;> rfl

/-- Actual resolved acquire definitions lie in this record's real fresh-register interval. -/
theorem stock_lower_acquire_resolved_defs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∀ m ∈ record.output.emitted.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))),
      ∀ key ∈ vdefs m,record.input.base.nextVreg ≤ key ∧ key < record.output.state.base.nextVreg := by
  obtain ⟨R,pointerReg,dest,resultId,key,register,results,resultReg,fresh,chunk,resultRegisters,finalAlias,finalNum⟩ :=
    stock_lower_acquire_selected_chunk run scope dominated events records recorded emitted selectedId
  have terminal := (stock_lower_freshAlias_terminal run (n := dest) (by
    rw [fresh]
    exact stock_lower_blockScanInitialFrontier run event events record records)).2
  have upper := stock_lower_acquire_record_frontier_step run scope dominated events records recorded emitted selectedId
  intro m member defined defMember
  rw [chunk] at member
  change m ∈ [(MInst.loadAcquire (CTy.ofClif R.ty) (.vreg dest .int) (.vreg pointerReg .int) R.flags).mapRegs
    (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))] at member
  have member := List.mem_singleton.mp member
  subst m
  change defined ∈ vdefs (.loadAcquire (CTy.ofClif R.ty)
    (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg dest .int))
    (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg pointerReg .int)) R.flags) at defMember
  rw [resolve_vreg,resolve_vreg] at defMember
  change defined ∈ vdefs (.loadAcquire (CTy.ofClif R.ty) (.vreg (aliasNum result.final.alias dest) .int)
    (.vreg (aliasNum result.final.alias pointerReg) .int) R.flags) at defMember
  rw [terminal] at defMember
  change defined ∈ [dest] at defMember
  have same : defined = dest := List.mem_singleton.mp defMember
  subst defined
  rw [fresh,upper]
  exact ⟨Nat.le_refl _,by omega⟩

end Backend.Stock.Proof.Acquire810
