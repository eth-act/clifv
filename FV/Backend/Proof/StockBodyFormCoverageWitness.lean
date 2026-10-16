import FV.Backend.Proof.StockBodyFormCoverage
import FV.Backend.Proof.StockFinalRecordFormsWitness

namespace Backend.Stock.Proof.BodyFormCoverageWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Backend.Proof.Spill Backend.Proof.PerEdgePrep
open Backend.Stock.Proof.EmissionCoverageFixture
open Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem source_not_term {f : Clif.Function} {result : Backend.Stock.Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} {info : IInfo} {inst : Clif.Inst}
    (source : event.ctx.insts[record.inst]? = some info) (original : info.clif = some inst) :
    record.inst ≠ event.termInst := by
  intro equal
  have actual : result.ctx.insts[event.termInst]? = some info := by
    rw [← equal]
    exact (stock_lower_record_context run scope events).2.2 _ _ _ source original
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  have origin := stock_lowerBlockCore_scanOrigin coreRun
  have contexts : event.ctx.insts = (Driver.termCtx result.ctx event.termInst data).insts := by
    rw [eventEq,origin.2.1,origin.2.2.2.1]
  have placeholder : event.ctx.insts[event.termInst]? = some ⟨data,[],[],none⟩ := by
    rw [contexts]
    exact termCtx_insts_self actual data
  rw [equal,placeholder] at source
  cases source
  cases original

/-- A complete original-input/raw/checked/physical pipeline has a nonempty
ordinary body, an actual retained source record and non-control instruction,
and the entire resolved body segment in the returned VCode. -/
theorem stock_body_form_coverage_witness :
    ∃ (result : Backend.Stock.Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc)
      (event : BlockScanEvent) (b : Clif.Block) (term record : ScanRecord) (body : BlockScan)
      (label k : Nat) (block : VBlock) (raw i : MInst),
      Stock.lower (function false) = .ok result ∧ LowerScope (function false) ∧
      Dominated (function false) ∧ ArityOk (function false) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      event ∈ result.blockScans.toList ∧ SourceBodySplit (function false) event b term body ∧
      record ∈ body.records ∧ raw ∈ record.output.emitted.toList ∧ raw ∈ body.code.toList ∧
      raw.isCtl = false ∧ Covered raw = true ∧ SpillInstOk raw ∧
      result.code.blocks[label]? = some block ∧
      SegAt block k (body.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ∧
      i ∈ body.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ∧
      i ∈ block.insts.toList ∧ i.isCtl = false ∧ Covered i = true ∧ SpillInstOk i ∧
      (∀ r ∈ body.records,∃ info inst,event.ctx.insts[r.inst]? = some info ∧ info.clif = some inst) ∧
      (∀ m ∈ body.code.toList,Covered m = true ∧ (m.isCtl = false → SpillInstOk m)) := by
  obtain ⟨result,p,rf,af,event,record,info,oldLabel,oldK,oldBlock,i,
    run,scope,dominated,arity,prepared,fallback,checked,physical,events,records,source,original,
    oldPlaced,oldSegment,recordMember,oldMember,ordinary,covered,static⟩ :=
    FinalRecordFormsWitness.stock_final_record_form_witness
  obtain ⟨b,term,body,label,block,k,split,placed,segment,sources,rawForms,finalForms⟩ :=
    Coverage.Result.stock_lower_body_form_coverage run scope events
  have bodyRecord : record ∈ body.records := by
    rw [split.records] at records
    rcases List.mem_cons.mp records with same | member
    · exact False.elim (source_not_term run scope events source original (same ▸ split.termInst))
    · exact member
  obtain ⟨raw,retained,resolved⟩ := List.mem_map.mp recordMember
  have rawMember : raw ∈ body.code.toList := by
    rw [split.scanned.code]
    exact List.mem_flatMap.mpr ⟨record,List.mem_reverse.mpr bodyRecord,retained⟩
  have rawOrdinary : raw.isCtl = false := by
    rw [← resolved,isCtl_mapRegs] at ordinary
    exact ordinary
  have bodyMember : i ∈ body.code.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) :=
    List.mem_map.mpr ⟨raw,rawMember,resolved⟩
  have actualMember : i ∈ block.insts.toList := by
    obtain ⟨j,found⟩ := List.mem_iff_getElem?.mp bodyMember
    obtain ⟨bounded,atIndex⟩ := List.getElem?_eq_some_iff.mp found
    exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? ((segment j bounded).trans (congrArg some atIndex)))
  have rawStatic := rawForms raw rawMember
  have finalStatic := finalForms i bodyMember
  exact ⟨result,p,rf,af,event,b,term,record,body,label,k,block,raw,i,
    run,scope,dominated,arity,prepared,fallback,checked,physical,events,split,bodyRecord,retained,rawMember,
    rawOrdinary,rawStatic.1,rawStatic.2 rawOrdinary,placed,segment,bodyMember,actualMember,
    ordinary,finalStatic.1,finalStatic.2 ordinary,sources,rawForms⟩

end Backend.Stock.Proof.BodyFormCoverageWitness
