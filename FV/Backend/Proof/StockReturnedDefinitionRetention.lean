import FV.Backend.Proof.StockDemandedScan
import FV.Backend.Proof.StockDivReturnDemand
import FV.Backend.Proof.StockDemandExtent

/-! The original return request protects a returned definition through every
intervening scan, removing the final-instruction restriction on returned division. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

private theorem mapped_member {ctx : Ctx} {xs : List Nat} {rs : List Reg}
    (mapping : xs.mapM ctx.valueReg? = some rs) {x : Nat} (member : x ∈ xs) :
    ∃ r,ctx.valueReg? x = some r := by
  induction xs generalizing rs with
  | nil => cases member
  | cons y ys ih =>
    simp only [List.mapM_cons,Option.bind_eq_bind,Option.bind_eq_some_iff,
      Option.pure_def,Option.some.injEq] at mapping
    obtain ⟨r,lookup,rest,tail,equal⟩ := mapping
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨r,lookup⟩
    · exact ih tail member

/-- Original mapped return operands have positive actual demand after the
real terminal helper. Bounds come from the whole driver, rather than a premise. -/
theorem stock_lower_return_positive_demand {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {xs : List Nat} (ret : b.term = .ret xs)
    {record : ScanRecord} (records : record ∈ event.output.records)
    (terminal : record.inst = event.termInst)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {x : Nat} (returned : x ∈ xs) : record.output.state.demand[x]! ≠ 0 := by
  obtain ⟨fuel,trace,rs,ps,enough,helper,root,mapped,pinned,state,code⟩ :=
    stock_lower_return_record_helper run scope events block ret records terminal recorded emitted
  have member : x ∈ xs ++ sretRet f := List.mem_append_left _ returned
  obtain ⟨r,lookup⟩ := mapped_member mapped member
  have bound := (Extent.lower_mapped_demand_bounds run scope events records lookup).1
  have scanBound : x < (scanState record.input record.inst).demand.size := by
    simpa only [scanState_demands] using bound
  have positive : (xs ++ sretRet f).count x ≠ 0 := by
    intro zero
    exact (List.count_eq_zero.mp zero) member
  rw [state]
  change ((xs ++ sretRet f).foldl State.mark (scanState record.input record.inst)).demand[x]! ≠ 0
  rw [markList_demand _ _ _ scanBound]
  omega

private theorem scans_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec exec indices input output) :
    ∀ record ∈ output.records,exec record.inst record.input = .ok record.output := by
  induction cert with
  | nil input => simp
  | cons head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member

/-- A returned division at any original source position is actually retained
and emitted. Every intervening scan preserves the demand-protected definition;
no whole-body no-sinking premise or final-position premise is supplied. -/
theorem stock_lower_returned_div_emitted {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {j : Nat} {stm : Clif.Stmt} (statement : b.body[j]? = some stm)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z]) :
    ∃ (term record : ScanRecord) (body : BlockScan) (step : Step),
      SourceBodySplit f event b term body ∧ record ∈ body.records ∧
      record.inst = blockStart f event.block+j ∧
      record.input.sunk[record.inst]! = false ∧
      scanInstruction event.ctx event.block record.inst event.termInst event.isBranch record.input = .ok record.output ∧
      record ∈ event.output.records ∧ record.output.step = some step ∧ step.decision = .emitted := by
  obtain ⟨term,body,termStep,split,member,unsunk,branch,recorded,emitted⟩ :=
    stock_lower_retTrap_emitted run scope events block (by rw [ret]; rfl)
  have defined : event.ctx.defInst? z = some (blockStart f event.block+j) :=
    stock_lower_source_result_definition run dominated events block statement (by simp [results])
  have safe := stock_lower_return_demand_unsunk run scope events block ret member
    split.termInst recorded emitted (by simp) defined
  have demanded := stock_lower_return_positive_demand run scope events block ret member
    split.termInst recorded emitted (by simp : z ∈ [z])
  have inside := (List.getElem?_eq_some_iff.mp statement).1
  have indexed : blockStart f event.block+j ∈ sourceBodyIndices f event.block b := by
    unfold sourceBodyIndices
    apply List.mem_reverse.mpr
    exact List.mem_map.mpr ⟨j,List.mem_range.mpr inside,rfl⟩
  rw [← split.scanned.order] at indexed
  obtain ⟨record,retained,current⟩ := List.mem_map.mp indexed
  obtain ⟨info,source,clif,infoResults⟩ :=
    ArithmeticBody.body_source_info run events split statement current
  have original : event.ctx.insts[blockStart f event.block+j]? = some info := by
    rw [← current]; exact source
  have resultMember : z ∈ event.ctx.insts[blockStart f event.block+j]!.results := by
    simp only [getElem!_def,original,Option.getD_some,infoResults,results,List.mem_singleton]
  obtain ⟨_,boundaries⟩ := stock_scans_demanded_unsunk split.scanned
  have kept := (boundaries record retained).1.2
    (blockStart f event.block+j) z resultMember demanded safe
  have safeHere : record.input.sunk[record.inst]! = false := by rw [current]; exact kept
  have mandatory : event.ctx.insts[record.inst]!.clif.any mustLower = true := by
    simp only [getElem!_def,source,Option.getD_some,clif,division,Option.any,mustLower]
  have ordinary : record.inst ≠ event.termInst := by rw [current,split.termIndex]; omega
  have actual := scans_execute split.scanned record retained
  obtain ⟨step,decision,actualEmitted⟩ := stock_mandatory_unsunk_emitted safeHere ordinary mandatory actual
  exact ⟨term,record,body,step,split,retained,current,safeHere,actual,
    split.retained record retained,decision,actualEmitted⟩

end Backend.Stock.Proof
