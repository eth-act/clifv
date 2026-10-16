import FV.Backend.Proof.StockFinalRecordForms
import FV.Backend.Proof.StockBindingCoverageWitness

namespace Backend.Stock.Proof.FinalRecordFormsWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Backend.Proof.Spill Backend.Proof.PerEdgePrep
open Backend.Stock.Proof.EmissionCoverageFixture
open Isle Isle.Interp Isle.Aarch64

/-- The final-alias and returned-segment roots are inhabited by a complete
original-input/raw/checked/physical pipeline and an actual non-control
instruction of its returned VCode. The retained source record is nonempty. -/
theorem stock_final_record_form_witness :
    ∃ (result : Backend.Stock.Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc)
      (event : BlockScanEvent) (record : ScanRecord) (info : IInfo)
      (label k : Nat) (block : VBlock) (i : MInst),
      Stock.lower (function false) = .ok result ∧ LowerScope (function false) ∧
      Dominated (function false) ∧ ArityOk (function false) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.iconst .i64 9) ∧
      result.code.blocks[label]? = some block ∧
      SegAt block k (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ∧
      i ∈ record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ∧
      i ∈ block.insts.toList ∧ i.isCtl = false ∧ Covered i = true ∧ SpillInstOk i := by
  obtain ⟨result,p,rf,af,n,out,after,trace,emission,event,record,info,rss,root,bound,fired,raw,
    run,scope,dominated,arity,prepared,fallback,checked,physical,named,register,registers,
    emitted,nonempty,forms,events,records,clean,source,original,results,rootRun,
    rssNonempty,pairsNonempty,binding,sameBase,retained,ordinary,covered,static⟩ :=
    BindingCoverageWitness.stock_bound_record_form_witness
  obtain ⟨label,block,k,placed,segment,finalForms⟩ :=
    Coverage.Result.stock_lower_source_record_final_segment run scope events records source original
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have member : raw.mapRegs resolve ∈ record.output.emitted.toList.map (·.mapRegs resolve) :=
    List.mem_map.mpr ⟨raw,retained,rfl⟩
  have inBlock : raw.mapRegs resolve ∈ block.insts.toList := by
    obtain ⟨j,found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨bounded,atIndex⟩ := List.getElem?_eq_some_iff.mp found
    exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? ((segment j bounded).trans (congrArg some atIndex)))
  have nonControl : (raw.mapRegs resolve).isCtl = false := by
    rw [isCtl_mapRegs]
    exact ordinary
  have finalStatic := finalForms (raw.mapRegs resolve) member
  exact ⟨result,p,rf,af,event,record,info,label,k,block,raw.mapRegs resolve,
    run,scope,dominated,arity,prepared,fallback,checked,physical,events,records,source,original,
    placed,segment,member,inBlock,nonControl,finalStatic.1,finalStatic.2 nonControl⟩

end Backend.Stock.Proof.FinalRecordFormsWitness
