import FV.Backend.Proof.StockFinalRecordForms
import FV.Backend.Proof.StockBodyScanOrigin

namespace Backend.Stock.Proof.Coverage.Result
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Backend.Proof.Spill
open Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Stock.runTerm lowerBlockCore

private theorem body_source {f : Clif.Function} {result : Backend.Stock.Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body) {record : ScanRecord}
    (records : record ∈ body.records) :
    ∃ info inst,event.ctx.insts[record.inst]? = some info ∧ info.clif = some inst := by
  obtain ⟨j,stm,statement,current⟩ := split.positions record records
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,oldState,legacy,spec,view⟩ := buildCtx_source build
  obtain ⟨info,source,clif,results⟩ := spec.facts.stmt event.block b j stm split.block statement
  have actual : result.ctx.insts[record.inst]? = some info := by
    rw [current,view.insts]
    exact source
  have different : record.inst ≠ event.termInst := by
    have bounded := (List.getElem?_eq_some_iff.mp statement).1
    rw [current,split.termIndex]
    omega
  have origin := stock_lowerBlockCore_scanOrigin coreRun
  have contexts : event.ctx.insts = (Driver.termCtx result.ctx event.termInst data).insts := by
    rw [eventEq,origin.2.1,origin.2.2.2.1]
  refine ⟨info,stm.inst,?_,clif⟩
  rw [contexts,termCtx_insts_ne different]
  exact actual

private theorem segment_of_factor {block : VBlock} {preludeCode code afterCode : Array MInst}
    (parts : block.insts = preludeCode ++ code ++ afterCode) : SegAt block preludeCode.size code.toList := by
  intro k hk
  have bound : k < code.size := by simpa using hk
  rw [parts,Array.append_assoc,Array.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [Array.getElem?_append_left bound]
  simp [bound]

/-- Every ordinary source body's actual emitted code has covered forms and
ordinary spill-static validity, including its final-alias segment in returned
VCode. Source slots, every scan decision, binding, and placement are derived
from the successful Stock run under the original source scope. -/
theorem stock_lower_body_form_coverage {f : Clif.Function} {result : Backend.Stock.Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ (b : Clif.Block) (term : ScanRecord) (body : BlockScan)
      (label : Nat) (block : VBlock) (k : Nat),
      SourceBodySplit f event b term body ∧ result.code.blocks[label]? = some block ∧
      SegAt block k (body.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ∧
      (∀ record ∈ body.records,∃ info inst,
        event.ctx.insts[record.inst]? = some info ∧ info.clif = some inst) ∧
      (∀ i ∈ body.code.toList,Covered i = true ∧ (i.isCtl = false → SpillInstOk i)) ∧
      (∀ i ∈ body.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))),
        Covered i = true ∧ (i.isCtl = false → SpillInstOk i)) := by
  obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split run scope events
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have raw : ∀ i ∈ body.code.toList,Covered i = true ∧ (i.isCtl = false → SpillInstOk i) := by
    intro i member
    rw [split.scanned.code] at member
    obtain ⟨record,inReverse,retained⟩ := List.mem_flatMap.mp member
    have records := List.mem_reverse.mp inReverse
    obtain ⟨info,inst,source,original⟩ := body_source run events split records
    exact stock_lower_source_record_form_coverage_original run scope events (split.retained record records)
      source original i retained
  have resolved : ∀ i ∈ body.code.toList.map (·.mapRegs resolve),
      Covered i = true ∧ (i.isCtl = false → SpillInstOk i) := by
    intro i member
    obtain ⟨raw,retained,rfl⟩ := List.mem_map.mp member
    rw [split.scanned.code] at retained
    obtain ⟨record,inReverse,inside⟩ := List.mem_flatMap.mp retained
    have records := List.mem_reverse.mp inReverse
    obtain ⟨info,inst,source,original⟩ := body_source run events split records
    exact stock_lower_resolved_source_record_form_coverage run scope events (split.retained record records)
      source original _ (List.mem_map.mpr ⟨raw,inside,rfl⟩)
  obtain ⟨label,block,preludeCode,afterCode,placed,code⟩ := stock_lower_block_scan_code run events
  have factor : block.insts = preludeCode ++ body.code.map (·.mapRegs resolve) ++
      (term.output.emitted.map (·.mapRegs resolve) ++ afterCode) := by
    simp only [code,split.code,Array.map_append,Array.append_assoc,resolve]
  exact ⟨b,term,body,label,block,preludeCode.size,split,placed,
    by simpa only [Array.toList_map] using segment_of_factor factor,
    fun record records => body_source run events split records,raw,resolved⟩

end Backend.Stock.Proof.Coverage.Result
