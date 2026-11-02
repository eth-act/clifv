import FV.Backend.Proof.StockHighMulSelected
import FV.Backend.Proof.StockRecordIntervals
namespace Backend.Stock.Proof.ScalarHighMul
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
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

/-- Actual narrow retained records allocate precisely four temporaries;
result binding preserves the allocation frontier. -/
theorem stock_lower_highmul_narrow_frontier {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (signed : Bool) {info : IInfo} {x y : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary (if signed then .smulhi else .umulhi) ty x y))
    (width : ty.width ≤ 32) {fr : Clif.Frame} (typed : FrameTyped event.ctx fr)
    {u v : BitVec ty.width} (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    record.output.state.base.nextVreg = record.input.base.nextVreg + 4 := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  obtain ⟨_,_,rx,ry,_,_,_,stateEq⟩ := stock_highmul_narrow_selected
    (stock_lower_record_context run scope events).1 signed source clif width typed getX getY receipt.selected
  have base := binding_base receipt.binding
  rw [receipt.state,base,stateEq]
  simp only [narrowBase,extendBase,finishBase,multiplyBase,LState.fresh,LState.emit,State.mark]
  unfold scanState
  dsimp only
  split <;> simp [Nat.add_assoc]

/-- The original availability invariant rules out capturing the second source
with the first narrow temporary. No extra source-contract condition is added. -/
theorem stock_lower_highmul_narrow_second_free {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (signed : Bool) {info : IInfo} {x y ny : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary (if signed then .smulhi else .umulhi) ty x y))
    (width : ty.width ≤ 32) {fr : Clif.Frame} (typed : FrameTyped event.ctx fr)
    {u v : BitVec ty.width} (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j)
    (available : y ∈ availOf f (availIn f result.ctx) bi j)
    (mapped : event.ctx.valueReg? y = some (.vreg ny .int)) :
    aliasNum result.final.alias ny ≠ record.input.base.nextVreg := by
  have frontier := stock_lower_highmul_narrow_frontier run scope events records signed
    source clif width typed getX getY recorded emitted
  have wholeMap : result.ctx.valueReg? y = some (.vreg ny .int) := by
    rw [← (stock_lower_record_context run scope events).2.1 y]; exact mapped
  have outside := stock_lower_available_alias_outside_record run scope dominated events records
    block statement current available wholeMap
  rw [frontier] at outside
  omega
end Backend.Stock.Proof.ScalarHighMul
