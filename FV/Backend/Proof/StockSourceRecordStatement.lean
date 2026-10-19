import FV.Backend.Proof.StockTermDataOrigin
import FV.Backend.Proof.StockBodyScanOrigin
namespace Backend.Stock.Proof.SourceRecordStatementDraft
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Every actual retained record with a source instruction has a real original
block/body position and the same source statement. No position or source-body
membership certificate is supplied by the caller. -/
theorem stock_lower_source_record_statement {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    {info : IInfo} {inst : Clif.Inst}
    (slot : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some inst) :
    ∃ (b : Clif.Block) (j : Nat) (stm : Clif.Stmt),f.blocks[event.block]? = some b ∧
      b.body[j]? = some stm ∧ record.inst = blockStart f event.block + j ∧ stm.inst = inst := by
  obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have bodyRecord : record ∈ body.records := by
    rw [split.records] at records
    rcases List.mem_cons.mp records with rfl | member
    · obtain ⟨original,data,block,prepared,termSlot⟩ := stock_lower_blockScan_term_data run scope events
      rw [split.termInst] at slot
      have same := Option.some.inj (slot.symm.trans termSlot)
      rw [same] at clif
      cases clif
    · exact member
  obtain ⟨j,stm,statement,current⟩ := split.positions record bodyRecord
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,oldState,legacy,spec,view⟩ := buildCtx_source build
  obtain ⟨other,source,otherClif,results⟩ := spec.facts.stmt event.block b j stm split.block statement
  have actual : result.ctx.insts[record.inst]? = some other := by
    rw [current,view.insts]
    exact source
  have globalSource := (stock_lower_record_context run scope events).2.2 record.inst info inst slot clif
  have same := Option.some.inj (actual.symm.trans globalSource)
  subst other
  exact ⟨b,j,stm,split.block,statement,current,Option.some.inj (otherClif.symm.trans clif)⟩
end Backend.Stock.Proof.SourceRecordStatementDraft
