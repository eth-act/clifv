import FV.Backend.Proof.StockAcquireSelectedCrossedReads

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Every actual event preserves the original successful build's statement slots. -/
theorem stock_lower_event_build_source_slots {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {original : Ctx} {ranges : Array (Nat × Nat)} {initial : LState}
    (built : Backend.buildCtx f = .ok (original,ranges,initial)) : SourceSlotsPreserved original event.ctx := by
  obtain ⟨actualRanges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initialState,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨other,otherState,otherBuilt,spec,view⟩ := buildCtx_source build
  have equal := Except.ok.inj (built.symm.trans otherBuilt)
  simp only [Prod.mk.injEq] at equal
  rcases equal with ⟨rfl,rfl,rfl⟩
  have actual := stock_lower_event_original_slots run scope events
  intro slot info inst installed source
  apply actual slot info inst _ source
  rw [view.insts]
  exact installed

/-- Every original colored statement belongs to the actual complete source-event list. -/
theorem original_colored_statement_event {f : Clif.Function} {original : Ctx}
    {ranges : Array (Nat × Nat)} {initial : LState}
    (built : Backend.buildCtx f = .ok (original,ranges,initial))
    {bi j : Nat} {block : Clif.Block} {stm : Clif.Stmt}
    (blockAt : f.blocks[bi]? = some block) (statement : block.body[j]? = some stm)
    (effect : Stock.colored stm.inst = true) :
    some (blockStart f bi+j) ∈ sourceColorEvents original ranges := by
  have spec := ctxSpec_of built
  rw [sourceColorEvents,spec.func]
  apply List.mem_flatMap.mpr
  refine ⟨(block,bi),List.mem_zipIdx_iff_getElem?.mpr blockAt,?_⟩
  apply (block_color_events_member built bi block blockAt _).mpr
  exact Or.inl ⟨stm,j,statement,effect,rfl⟩

end Backend.Stock.Proof.Acquire810
