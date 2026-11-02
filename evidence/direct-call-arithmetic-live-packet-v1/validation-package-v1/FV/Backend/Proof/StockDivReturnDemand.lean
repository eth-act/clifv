import FV.Backend.Proof.StockReturnRecordCalls
import FV.Backend.Proof.StockTerminalEmission
import FV.Backend.Proof.StockArithmeticBodyRefines

/-! Derive division retention from the real return request. This uses the
original source SSA and successful driver execution, including arbitrary
zero/overflow inputs; it does not classify division as a pure instruction. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

/-- A source result keeps its original definition in the actual block context. -/
theorem stock_lower_source_result_definition {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {bi j x : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (member : x ∈ stm.results) : event.ctx.defInst? x = some (blockStart f bi + j) := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,
    label,nodeBi,data,core,build,ordered,initial,empty,parts,folded,
    final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,st0,oldBuild,spec,view⟩ := buildCtx_source build
  have defs : event.ctx.valDef = original.valDef := by
    rw [eventEq,(stock_lowerBlockCore_scanOrigin coreRun).2.1]
    exact view.valDef
  simpa only [Ctx.defInst?,defs] using
    (defInst_res spec.facts dominated.ssa block statement member)

private theorem mark_sunk (xs : List Nat) (st : State) :
    (xs.foldl State.mark st).sunk = st.sunk := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => exact ih (st.mark x)

private theorem scan_preserves_sunk (st : State) (i : Nat) : (scanState st i).sunk = st.sunk := by
  unfold scanState
  dsimp only
  split <;> rfl

/-- The actual return helper leaves every returned definition unsunk in the
state passed to the ordinary body. Safety is derived from its real requests. -/
theorem stock_lower_return_demand_unsunk {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {xs : List Nat} (ret : b.term = .ret xs)
    {record : ScanRecord} (records : record ∈ event.output.records)
    (terminal : record.inst = event.termInst)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {x i : Nat} (returned : x ∈ xs) (defined : event.ctx.defInst? x = some i) :
    record.output.state.sunk[i]! = false := by
  obtain ⟨fuel,trace,rs,ps,enough,helper,root,mapped,pinned,state,code⟩ :=
    stock_lower_return_record_helper run scope events block ret records terminal recorded emitted
  obtain ⟨rs',ps',safe,mapped',pins',state',out⟩ :=
    stock_lower_return_observed data_program rfl enough helper
  have allowed := safe x (List.mem_append_left _ returned) i defined
  rw [state]
  change ((xs ++ sretRet f).foldl State.mark (scanState record.input record.inst)).sunk[i]! = false
  rw [mark_sunk,scan_preserves_sunk]
  simpa only [scan_preserves_sunk] using allowed

/-- Mandatory ordinary instructions cannot take omitted/opportunistic paths. -/
theorem stock_mandatory_unsunk_emitted {ctx : Ctx} {block i ti : Nat} {branch : Bool}
    {input : State} {output : Scan} (unsunk : input.sunk[i]! = false) (ordinary : i ≠ ti)
    (mandatory : ctx.insts[i]!.clif.any mustLower = true)
    (run : scanInstruction ctx block i ti branch input = .ok output) :
    ∃ step, output.step = some step ∧ step.decision = .emitted := by
  unfold scanInstruction at run
  have notTerm : (i == ti) = false := by simp [ordinary]
  simp only [unsunk,Bool.false_eq_true,ite_false,notTerm,Bool.false_and,
    mandatory,Bool.not_true,Bool.and_false] at run
  cases call : emitInstruction ctx i (scanState input i) with
  | error e => simp only [call,bind,Except.bind] at run; cases run
  | ok emission =>
    simp only [call,bind,Except.bind,pure,Except.pure] at run
    cases run
    exact ⟨_,rfl,rfl⟩

/-- A single original division returned by the source is actually emitted.
The record, result demand and mandatory decision are all derived internally. -/
theorem stock_lower_single_div_return_emitted {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {stm : Clif.Stmt} (singleton : b.body = [stm])
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z]) :
    ∃ (term record : ScanRecord) (body : BlockScan) (step : Step),
      SourceBodySplit f event b term body ∧ body.records = [record] ∧
      record.inst = blockStart f event.block ∧ record.input = term.output.state ∧
      scanInstruction event.ctx event.block record.inst event.termInst event.isBranch record.input = .ok record.output ∧
      record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted := by
  obtain ⟨term,body,termStep,split,member,unsunk,branch,recorded,emitted⟩ :=
    stock_lower_retTrap_emitted run scope events block (by rw [ret]; rfl)
  have statement : b.body[0]? = some stm := by simp [singleton]
  have defined : event.ctx.defInst? z = some (blockStart f event.block) := by
    simpa only [Nat.add_zero] using stock_lower_source_result_definition run dominated events
      block statement (by simp [results])
  have safe := stock_lower_return_demand_unsunk run scope events block ret member
    split.termInst recorded emitted (by simp) defined
  have scanned := split.scanned
  simp only [sourceBodyIndices,singleton,List.length_cons,List.length_nil,List.range_succ,
    List.range_zero,List.nil_append,List.map_cons,List.map_nil,List.reverse_cons,
    List.reverse_nil,List.nil_append,Nat.add_zero] at scanned
  cases scanned with
  | cons head rest =>
    cases rest
    rename_i scan
    let record : ScanRecord := ⟨blockStart f event.block,term.output.state,scan⟩
    have current : record.inst = blockStart f event.block + 0 := by rfl
    obtain ⟨info,source,clif,infoResults⟩ := ArithmeticBody.body_source_info run events split statement current
    have mandatory : event.ctx.insts[record.inst]!.clif.any mustLower = true := by
      simp only [getElem!_def,source,Option.getD_some,clif,division,Option.any,mustLower]
    have ordinary : record.inst ≠ event.termInst := by
      rw [split.termIndex,singleton]
      change blockStart f event.block ≠ blockStart f event.block + 1
      omega
    obtain ⟨step,decision,actual⟩ := stock_mandatory_unsunk_emitted safe ordinary mandatory head
    exact ⟨term,record,_,step,split,rfl,rfl,rfl,head,
      split.retained record (by simp [record]),decision,actual⟩

end Backend.Stock.Proof
