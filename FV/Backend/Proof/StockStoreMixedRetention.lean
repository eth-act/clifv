import FV.Backend.Proof.StockStoreRetention
import FV.Backend.Proof.StockProtectedSinkDriver

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

/-- Actual body positions identify the original table entry before terminator replacement. -/
theorem stock_lower_original_body_info {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body) {j : Nat} {stm : Clif.Stmt}
    (statement : b.body[j]? = some stm) :
    ∃ info,result.ctx.insts[blockStart f event.block+j]? = some info ∧
      info.clif = some stm.inst ∧ info.results = stm.results := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,
    label,bi,data,core,build,ordered,initial,empty,parts,folded,
    final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,st0,oldBuild,spec,view⟩ := buildCtx_source build
  obtain ⟨info,found,clif,results⟩ := spec.facts.stmt event.block b j stm split.block statement
  refine ⟨info,?_,clif,results⟩
  rw [view.insts]
  exact found

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

/-- Every original store is retained and emitted beside arbitrary other admitted instructions.
The block may end in any admitted terminator. No global no-load condition is needed. -/
theorem stock_lower_mixed_store_emitted {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {j : Nat} {op : Clif.StoreOp} {ty : Clif.Ty} {flags : Clif.MemFlags}
    {value pointer : Nat} {offset : Int}
    (statement : b.body[j]? = some ⟨[],.store op ty flags value pointer offset⟩) :
    ∃ (term record : ScanRecord) (body : BlockScan) (step : Step),
      SourceBodySplit f event b term body ∧ record ∈ body.records ∧
      record.inst = blockStart f event.block+j ∧
      record.input.sunk[record.inst]! = false ∧
      scanInstruction event.ctx event.block record.inst event.termInst event.isBranch record.input = .ok record.output ∧
      record ∈ event.output.records ∧ record.output.step = some step ∧ step.decision = .emitted := by
  obtain ⟨original,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have same : original = b := Option.some.inj (split.block.symm.trans block)
  subst original
  have inside := (List.getElem?_eq_some_iff.mp statement).1
  have indexed : blockStart f event.block+j ∈ sourceBodyIndices f event.block b := by
    unfold sourceBodyIndices
    apply List.mem_reverse.mpr
    exact List.mem_map.mpr ⟨j,List.mem_range.mpr inside,rfl⟩
  rw [← split.scanned.order] at indexed
  obtain ⟨record,retained,current⟩ := List.mem_map.mp indexed
  obtain ⟨info,source,clif,infoResults⟩ := ArithmeticBody.body_source_info run events split statement current
  obtain ⟨originalInfo,originalFound,originalClif,_⟩ := stock_lower_original_body_info run events split statement
  have root : result.ctx.insts[record.inst]? = some originalInfo := by rw [current]; exact originalFound
  have safeHere : record.input.sunk[record.inst]! = false :=
    (((SinkRules.stock_lower_store_unsunk run scope root originalClif).2 event events).2
      record (split.retained record retained)).1
  have ordinary : record.inst ≠ event.termInst := by rw [current,split.termIndex]; omega
  have actual := scans_execute split.scanned record retained
  obtain ⟨step,decision,which⟩ := stock_ordinary_unsunk_decision safeHere ordinary actual
  have actualEmitted : step.decision = .emitted := by
    rcases which with omitted | remembered | emitted
    · have mandatory := (scan_omitted actual decision omitted).2.1
      simp [getElem!_def,source,clif,mustLower] at mandatory
    · exact False.elim ((Coverage.lower_record_noOpportunistic scope run events
        (split.retained record retained) decision) remembered)
    · exact emitted
  exact ⟨term,record,body,step,split,retained,current,safeHere,actual,
    split.retained record retained,decision,actualEmitted⟩

end Backend.Stock.Proof
