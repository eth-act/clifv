import FV.Backend.Proof.StockAcquireFallbackFrozenStep
import FV.Backend.Proof.StockAcquireRequestedPendingValue
import FV.Backend.Proof.StockDemandExtent

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Actual selected fallback execution derives the complete emitted extension from compiler types.
The theorem does not assume that the original source extension succeeds or widens. -/
theorem fallback_extend_selected_demand_allowed {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (signed : Bool) {i x : Nat} {info : IInfo} {target : Clif.Ty}
    (installed : ctx.insts[i]? = some info)
    (source : info.clif = some (.extend (ScalarCast.extendOp signed) target x))
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx i st out next rules) (chosen : selected.rule = ScalarCast.extendRule signed) :
    DemandAllowed ctx st x := by
  obtain ⟨small,data,type⟩ := fallback_extend_source_data inv signed installed source
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]
    decide +kernel
  have enough := selected.fuelBound
  rw [count] at enough
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+10 := ⟨selected.matchFuel-10,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq] at matched
  cases typed : ctx.valueType? x with
  | none =>
    exact False.elim (ScalarCast.stock_extend_match_no_type data_program ctx signed installed type data typed
      st selected.matched #[] selected.matchTrace m selected.env matched)
  | some sourceType =>
    rw [ScalarCast.stock_extend_match data_program ctx signed installed type data typed st #[] m,if_pos small] at matched
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
    obtain ⟨envEq,stateEq,traceEq⟩ := matched
    have rhs := selected.rhsRun
    rw [chosen,← envEq,← stateEq,← traceEq] at rhs
    change (evalExpr program (Stock.sem ctx) {} (999959+40) (ScalarCast.extendRule signed).rhs
      (envExt target.width x sourceType)).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
    exact (ScalarCast.stock_extend_rhs_requests data_program ctx signed rhs).1

/-- Actual fallback selection derives both the request safety and its nonzero demand.
No caller supplies a register request or a demand certificate. -/
theorem stock_lower_fallback_extend_operand_guard {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (signed : Bool) {info : IInfo} {target : Clif.Ty} {x : Nat}
    (installed : event.ctx.insts[record.inst]? = some info)
    (source : info.clif = some (.extend (ScalarCast.extendOp signed) target x))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (ScalarCast.extendRule signed).id) :
    DemandAllowed event.ctx record.output.state x ∧ Demanded record.output.state x := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have last : receipt.fired.getLast? = some (ScalarCast.extendRule signed).id := by
    rw [← receipt.rules]
    exact selectedId
  have chosen := fallback_extend_selected_rule signed receipt.selected last
  have mapped := (stock_lower_record_context run scope events).1
  have safe := fallback_extend_selected_demand_allowed mapped signed installed source receipt.selected chosen
  obtain ⟨sourceType,pointer,typed,accepted,register,output,nextEq⟩ :=
    fallback_extend_selected_shape mapped signed installed source receipt.selected chosen
  have sunk := stock_lower_fallback_extend_sunk_frame run scope events records signed installed source recorded emitted selectedId
  have demand : record.output.state.demand = ((scanState record.input record.inst).mark x).demand := by
    rw [receipt.state,stock_bindResults_demand receipt.binding,nextEq]
  have bound := (Extent.lower_mapped_demand_bounds run scope events records register).1
  have scanDemand : (scanState record.input record.inst).demand = record.input.demand := by
    unfold scanState
    dsimp only
    split <;> rfl
  have inside : x < (scanState record.input record.inst).demand.size := by rw [scanDemand];exact bound
  constructor
  · intro producer defined
    have unmarked := safe producer defined
    rw [scanState_sunk] at unmarked
    simpa only [sunk] using unmarked
  · change record.output.state.demand[x]! ≠ 0
    rw [demand]
    exact (demanded_mark_iff _ x x inside).mpr (Or.inl rfl)

/-- Actual fallback operands recover their binding from the general pending invariant.
Original dominance supplies availability; actual selection supplies request safety and demand. -/
theorem stock_lower_fallback_extend_pending_operand {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (signed : Bool) {info : IInfo} {target : Clif.Ty} {x : Nat}
    (installed : event.ctx.insts[record.inst]? = some info)
    (source : info.clif = some (.extend (ScalarCast.extendOp signed) target x))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (ScalarCast.extendRule signed).id)
    {j : Nat} {block : Clif.Block} {statement : Clif.Stmt}
    (blockAt : f.blocks[event.block]? = some block) (statementAt : block.body[j]? = some statement)
    (current : record.inst = blockStart f event.block+j)
    {env : Clif.Env} {program : Clif.Program} {frontier : ReadEffectFrontier event.ctx env program}
    (retained : ∀ captured ∈ frontier.history,captured.record ∈ event.output.records)
    (marked : PendingReadMarks frontier record.output.state)
    (retired : RetiredUndemanded frontier record.output.state)
    {MR : MemRelT} {point : Clif.Frame × Clif.Mem} {regs : Nat → CV} {world : Arm.ArmState}
    (prior : PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history
      record.output.state (j,point) regs world) :
    ValueHeld event.ctx point.1 (fun key => regs (aliasNum result.final.alias key)) x := by
  obtain ⟨allowed,demand⟩ := stock_lower_fallback_extend_operand_guard run scope events records signed installed source
    recorded emitted selectedId
  have available := stock_lower_record_args_available run scope dominated events blockAt statementAt current installed source
    x (by cases signed <;> simp [ScalarCast.extendOp,Driver.instArgs])
  have pendingValues := frontier_pending_values prior.2.2.2 retired
  have pendingRetained : ∀ captured ∈ frontier.pending,captured.record ∈ event.output.records := by
    intro captured member
    apply retained captured
    rw [frontier.split]
    exact List.mem_append_right _ member
  have notSuspended := stock_lower_allowed_not_suspended run scope dominated events pendingRetained marked allowed
  exact pendingValues x ⟨demand,available⟩ notSuspended

end Backend.Stock.Proof.Acquire810
