import FV.Backend.Proof.StockAcquireReadMarked
import FV.Backend.Proof.StockRecordContext

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Every actual scan context preserves all original statement slots across its terminator replacement. -/
theorem stock_lower_event_original_slots {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) : SourceSlotsPreserved result.ctx event.ctx := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  have nonempty : f.blocks.length ≠ 0 := fun h => scope.nonempty (List.length_eq_zero_iff.mp h)
  have labelBound := (stock_backward_suffix_split parts).1
  have lookup : result.order.nodes[label]? = some (.original bi) := by
    rw [getElem!_pos result.order.nodes label labelBound] at node
    simp only [Array.getElem?_eq_getElem labelBound,node]
  have valid := (stock_blockOrder_originals_nodup ordered nonempty).2
  have projected : bi ∈ stockOriginals result.order.nodes := by
    unfold stockOriginals
    apply List.mem_filterMap.mpr
    exact ⟨.original bi,Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup),rfl⟩
  have biBound := valid bi projected
  have block : f.blocks[bi]? = some f.blocks[bi] := by simp [biBound]
  obtain ⟨original,oldState,oldBuild,spec,view⟩ := buildCtx_source build
  have range := spec.ranges bi f.blocks[bi] block
  have rangeValue : ranges[bi]! = (blockStart f bi,blockStart f bi+f.blocks[bi].body.length+1) := by
    simp only [getElem!_def,range]
  have placeholder : result.ctx.insts[ranges[bi]!.2-1]? = some ⟨.op .unit,[],[],none⟩ := by
    rw [rangeValue]
    have terminal : blockStart f bi+f.blocks[bi].body.length+1-1 = blockStart f bi+f.blocks[bi].body.length := by omega
    rw [terminal,view.insts]
    exact spec.facts.term bi f.blocks[bi] block
  rw [eventEq,(stock_lowerBlockCore_scanOrigin coreRun).2.1]
  exact (source_slots_termCtx placeholder data).withTryRegs _

end Backend.Stock.Proof.Acquire810
