import FV.Backend.Proof.StockAcquirePreparedRecordOrigin

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch collectOutgoing scanBlock

/-- Actual core execution retains its original source branch classification. -/
theorem blockCore_source_branch {ctx : Ctx} {order : Order} {f : Clif.Function} {block : Clif.Block}
    {bi start stop : Nat} {data : Backend.V} {targets : Array Nat} {input : State} {core : LoweredBlockCore}
    (run : lowerBlockCore ctx order f block bi start stop data targets input = .ok core) :
    core.scan.isBranch = Coverage.blockBranch block.term := by
  unfold lowerBlockCore at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run; simp_all [Coverage.blockBranch]

/-- Prepared data and original ranges classify every actual retained slot internally. -/
theorem stock_lower_record_source_slot {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records) :
    Coverage.ScanSlot event.ctx record.inst event.termInst event.isBranch := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initialState,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,prepared,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin_prepared run events
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
  have blockAt : f.blocks[bi]? = some f.blocks[bi]! := by simp [getElem!_def,biBound]
  obtain ⟨original,st0,oldBuild,spec,view⟩ := buildCtx_source build
  have rangeAt := spec.ranges bi f.blocks[bi]! blockAt
  have slots := Coverage.built_scan_slots build scope blockAt rangeAt prepared before.state.tryRegs[ranges[bi]!.2-1]!
  have origin := stock_lowerBlockCore_scanOrigin coreRun
  have actual := runScans_spec (stock_lower_event_scan_run run events)
  have instMember : record.inst ∈ event.indices := by
    rw [← ScansSpec.record_indices actual]
    exact List.mem_map.mpr ⟨record,records,rfl⟩
  have eventSlots : ∀ inst ∈ event.indices,Coverage.ScanSlot event.ctx inst event.termInst event.isBranch := by
    rw [eventEq,origin.2.1,origin.2.2.2.1,origin.2.2.2.2.1,blockCore_source_branch coreRun]
    have rangeValue : ranges[bi]! = (blockStart f bi,blockStart f bi+f.blocks[bi]!.body.length+1) := by
      simp only [getElem!_def,rangeAt]
    simpa only [rangeValue] using slots
  exact eventSlots record.inst instMember

end Backend.Stock.Proof.Acquire810
