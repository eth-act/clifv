import FV.Backend.Proof.StockCallRecordSource
import FV.Backend.Proof.StockDemandExtent
import FV.Backend.Proof.StockAluOperandCoverage
namespace Backend.Stock.Proof.CallRecordFootprintDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open CallRhsCallsDraft CallRecordCallsDraft CallResultBindingDraft TupleBindingDraft TupleRecordBindingDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem domain {α β : Type} (f : α → Option β) (xs : List α) {ys : List β}
    (run : xs.mapM f = some ys) : ∀ x ∈ xs,∃ y,f x = some y := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    rw [List.mapM_cons] at run
    cases head : f x with
    | none => simp [head] at run
    | some y =>
      cases tail : xs.mapM f with
      | none => simp [head,tail] at run
      | some zs =>
        intro z member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨y,head⟩
        · exact ih tail z member
private theorem scan_demand (st : State) (i : Nat) : (scanState st i).demand = st.demand := by
  unfold scanState; dsimp only; split <;> rfl
private theorem scan_frontier (st : State) (i : Nat) : (scanState st i).base.nextVreg = st.base.nextVreg := by
  unfold scanState; dsimp only; split <;> rfl

/-- The SAME actual call RHS internally demands every source argument and
allocates the complete explicit result interval. All helper preservation,
request bounds and binder facts are derived from the retained record. -/
theorem stock_lower_direct_call_record_footprint {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup) (abi : AbiSigsOk f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {info : IInfo} {fn : Nat} {args : List Nat} {ext : Clif.ExtFunc}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.call fn args))
    (external : f.extern? fn = some ext) (colocated : ext.colocated = true)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    record.input.base.nextVreg + ext.sig.returns.length ≤ record.output.state.base.nextVreg ∧
      ∀ x ∈ args,Demanded record.output.state x := by
  obtain ⟨receipt,chosen,last,environment,state,trace,calls⟩ := stock_lower_direct_call_record_calls
    run scope events records slot clif external colocated recorded emitted
  have mapped := (stock_lower_record_context run scope events).1
  have vectors := (stock_lower_call_result_binding run scope ssa abi events records slot clif external recorded emitted).2.1
  have binding := receipt.binding
  have bang : event.ctx.insts[record.inst]! = info := by simp only [getElem!_def,slot]
  rw [bang,receipt.resultRegs.symm.trans vectors] at binding
  have installed := stock_bindResults_fresh_tuple mapped (stock_lower_record_results_nodup run scope ssa events slot clif) binding
  obtain ⟨outs,afterOut,abiValue,afterAbi,requested,afterRequest,uses,afterArgs,defs,afterDefs,noTry,afterNone,
    callInfo,afterInfo,machine,afterMachine,machineTrace,unit,afterEmit,emitTrace,callFuel,emitFuel,
    output,abiRun,request,arguments,returns,noneRun,formed,callBound,emitBound,machineCall,emission,outputRun,traceEq⟩ := calls
  have a0 := (stock_ctor_allocationLe abiRun).1
  have a1 := (stock_ctor_allocationLe request).1
  have a2 := (stock_ctor_allocationLe arguments).1
  have a3 := (stock_ctor_allocationLe returns).1
  have a4 := (stock_ctor_allocationLe noneRun).1
  have a5 := (stock_ctor_allocationLe formed).1
  have a6 := (stock_apply_allocationLe machineCall).1
  have a7 := (stock_apply_allocationLe emission).1
  have a8 := (stock_ctor_allocationLe outputRun).1
  have outputShape := output
  rw [CallOutputStaticDraft.stock_gen_call_output_exact] at outputShape
  cases outputShape
  have allocated : record.input.base.nextVreg + ext.sig.returns.length ≤ record.output.state.base.nextVreg := by
    rw [receipt.state,installed.2.1]
    simp only [freshN_nextVreg,scan_frontier] at a0
    omega
  refine ⟨allocated,?_⟩
  obtain ⟨safe,rs,mapping,requestedEq,requestState⟩ := (stock_put_in_regs_vec_iff _ _ _ _ _).mp request
  intro x member
  obtain ⟨r,lookup⟩ := domain event.ctx.valueReg? args mapping x member
  have bound := (Extent.lower_mapped_demand_bounds run scope events records lookup).1
  have abiSize := Extent.ctor_demand_size abiRun
  have outputSize := Extent.ctor_demand_size output
  have size : afterAbi.demand.size = record.input.demand.size := by
    rw [abiSize,outputSize,scan_demand]
  have wanted : Demanded afterRequest x := by
    rw [requestState]
    exact (demanded_markList_iff _ args x (by rw [size]; exact bound)).2 (.inl member)
  have d0 := stock_ctor_demand_mono arguments x
  have d1 := stock_ctor_demand_mono returns x
  have d2 := stock_ctor_demand_mono noneRun x
  have d3 := stock_ctor_demand_mono formed x
  have d4 := stock_apply_demand_mono machineCall x
  have d5 := stock_apply_demand_mono emission x
  have d6 := stock_ctor_demand_mono outputRun x
  have binder := stock_bindResults_demand receipt.binding
  intro zero
  change record.output.state.demand[x]! = 0 at zero
  rw [receipt.state,binder] at zero
  change afterRequest.demand[x]! ≠ 0 at wanted
  omega

/-- The original dominance condition and actual selected requests place EVERY
call argument in the demanded-and-available source guard at its real position. -/
theorem stock_lower_direct_call_operand_coverage {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f) (abi : AbiSigsOk f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi + j)
    {info : IInfo} {fn : Nat} {args : List Nat} {ext : Clif.ExtFunc}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.call fn args))
    (external : f.extern? fn = some ext) (colocated : ext.colocated = true)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∀ x ∈ args,Demanded record.output.state x ∧ x ∈ availOf f (availIn f result.ctx) bi j := by
  intro x member
  exact ⟨(stock_lower_direct_call_record_footprint run scope dominated.ssa abi events records slot clif external colocated recorded emitted).2 x member,
    stock_lower_record_args_available run scope dominated events block statement current slot clif x member⟩
end Backend.Stock.Proof.CallRecordFootprintDraft
