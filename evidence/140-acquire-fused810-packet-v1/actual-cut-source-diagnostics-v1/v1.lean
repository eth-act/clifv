import FV.Backend.Proof.StockAcquireReadQueueRecord
import FV.Backend.Proof.StockTerminalDriver

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle
set_option autoImplicit false
set_option Elab.async false

/-- Actual traversal supplies the original range, first unsunk terminator, and complete source-color table. -/
theorem stock_lower_event_cut_source {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState) (bi : Nat) (block : Clif.Block),
      Backend.buildCtx f = .ok (original,ranges,initial) ∧ f.blocks[bi]? = some block ∧
      event.termInst = blockStart f bi+block.body.length ∧
      event.indices = event.termInst::((Array.range block.body.length).map (blockStart f bi+·)).reverse.toList ∧
      some event.termInst ∈ sourceColorEvents original ranges ∧ event.input.sunk[event.termInst]! = false ∧
      event.input.entryColor = (sourceMetadata original ranges).entryColor ∧
      ∀ record ∈ event.output.records,record.input.entryColor = (sourceMetadata original ranges).entryColor := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initialState,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
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
  have blockAt : f.blocks[bi]? = some f.blocks[bi] := by simp [biBound]
  obtain ⟨original,st0,requests,oldBuild,allocation,finish⟩ := buildCtx_allocation build
  have spec := ctxSpec_of oldBuild
  have range := spec.ranges bi f.blocks[bi] blockAt
  have rangeValue : ranges[bi]! = (blockStart f bi,blockStart f bi+f.blocks[bi].body.length+1) := by
    simp only [getElem!_def,range]
  have termEq : event.termInst = blockStart f bi+f.blocks[bi].body.length := by
    rw [eventEq,(stock_lowerBlockCore_scanOrigin coreRun).2.2.2.1,rangeValue]
    omega
  have indicesEq : event.indices = event.termInst::
      ((Array.range f.blocks[bi].body.length).map (blockStart f bi+·)).reverse.toList := by
    rw [eventEq,(stock_lowerBlockCore_scanOrigin coreRun).2.2.2.2.1,rangeValue]
    have count : blockStart f bi+f.blocks[bi].body.length+1-blockStart f bi = f.blocks[bi].body.length+1 := by omega
    rw [count,scan_indices_head]
    rw [← eventEq,termEq]
  have insts : result.ctx.insts = original.insts := congrArg (fun q : Ctx × Array (Nat × Nat) × State => q.1.insts) finish
  have initialColors : result.initial.entryColor = (sourceMetadata original ranges).entryColor :=
    congrArg (fun q : Ctx × Array (Nat × Nat) × State => q.2.2.entryColor) finish
  have placeholder : result.ctx.insts[event.termInst]? = some ⟨.op .unit,[],[],none⟩ := by
    rw [termEq,insts]
    exact spec.facts.term bi f.blocks[bi] blockAt
  have noSource : result.ctx.insts[event.termInst]!.clif = none := by
    simp only [getElem!_def,placeholder,Option.getD_some]
  have termUnsunk := (Coverage.Preservation.stock_lower_records_terminal_unsunk scope run events).1 event.termInst noSource
  have terminalSource : some event.termInst ∈ sourceColorEvents original ranges := by
    unfold sourceColorEvents
    rw [spec.func]
    apply List.mem_flatMap.mpr
    refine ⟨(f.blocks[bi],bi),List.mem_zipIdx_iff_getElem?.mpr blockAt,?_⟩
    have terminal : ranges[bi]!.2-1 = event.termInst := by rw [rangeValue,termEq]; omega
    simp [blockColorEvents,terminal]
  refine ⟨original,ranges,st0,bi,f.blocks[bi],oldBuild,blockAt,termEq,indicesEq,terminalSource,termUnsunk,?_,?_⟩
  · exact ((stock_lower_zeroColorLe run).2 event events).1.1.trans initialColors
  · intro record records
    exact (((stock_lower_zeroColorLe run).2 event events).2 record records).1.1.trans initialColors

end Backend.Stock.Proof.Acquire810
