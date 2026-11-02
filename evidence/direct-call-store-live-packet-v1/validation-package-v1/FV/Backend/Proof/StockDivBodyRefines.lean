import FV.Backend.Proof.StockDivReturnDemand
import FV.Backend.Proof.StockDivScanRefines
namespace Backend.Stock.Proof.DivBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- The returned division derives its actual retained binder and virtual
integer destination. No chosen record or result mapping comes from the input. -/
theorem actual_single_div_record {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {stm : Clif.Stmt} (singleton : b.body = [stm])
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z]) :
    ∃ (term record : ScanRecord) (body : BlockScan) (step : Step) (info : IInfo) (a : Nat),
      SourceBodySplit f event b term body ∧ body.records = [record] ∧
      record.inst = blockStart f event.block ∧ record.input = term.output.state ∧
      record ∈ event.output.records ∧ record.output.step = some step ∧ step.decision = .emitted ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.div op ty x y) ∧
      info.results = [z] ∧ event.ctx.valueReg? z = some (.vreg a .int) := by
  obtain ⟨term,record,body,step,split,records,current,input,scan,member,recorded,emitted⟩ :=
    stock_lower_single_div_return_emitted run scope dominated events block singleton division results ret
  have statement : b.body[0]? = some stm := by simp [singleton]
  obtain ⟨info,source,clif,infoResults⟩ := ArithmeticBody.body_source_info run events split
    statement (by simpa using current)
  obtain ⟨emission,emissionRun,scanEq⟩ := stock_emitted_scan scan recorded emitted
  obtain ⟨r,mapped⟩ := ArithmeticBody.emission_result_mapped (z := z) emissionRun
    (by simp only [getElem!_def,source,Option.getD_some,infoResults,results])
  have inv := (stock_lower_record_context run scope events).1
  obtain ⟨a,rfl⟩ := inv.valueReg z r mapped
  exact ⟨term,record,body,step,info,a,split,records,current,input,member,recorded,emitted,
    source,by rwa [division] at clif,infoResults.trans results,mapped⟩

/-- Compose a successful original division source step with its complete real
body chunk and guarded post-state. The trapping case is proved separately. -/
theorem actual_single_div_body_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {stm : Clif.Stmt} (singleton : b.body = [stm])
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z])
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ∃ term body, SourceBodySplit f event b term body ∧
      ∀ s s', SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block + ·)) s s' →
        ∀ ρ w, GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w → ∃ ρ' w',
          seqRun isem (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ w =
            some (.fall ρ' w') ∧
          GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' w' := by
  obtain ⟨term,record,body,step,info,a,split,records,current,input,member,recorded,emitted,
    source,clif,infoResults,mapped⟩ := actual_single_div_record run scope dominated events block
      singleton division results ret
  have statement : b.body[0]? = some stm := by simp [singleton]
  have localRun := stock_lower_div_scan_fall_refines run scope dominated events member block statement
    (by simpa using current) op source clif infoResults results mapped recorded emitted refines stable (env := env) (cp := cp)
  refine ⟨term,body,split,?_⟩
  intro s s' steps ρ w held
  apply split.scanned.fall_refines (source := IndexedSourceInst env cp f event.ctx event.block) (sem := isem) (aliases := result.final.alias)
    (rel := GuardedScanRel f result event.ctx event.block MR) ?_ s s' ?_ ρ w ?_
  · intro r present
    have same : r = record := by simpa only [records,List.mem_singleton] using present
    subst r
    simpa only [input] using localRun
  · simpa only [sourceBodyIndices,List.reverse_reverse] using steps
  · simpa only [split.state] using held

end Backend.Stock.Proof.DivBody
