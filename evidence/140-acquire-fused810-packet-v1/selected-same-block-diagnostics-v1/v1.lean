import FV.Backend.Proof.StockAcquireTermSourceBoundary

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual selected root810 derives its atomic producer's original body position in the consumer block. -/
theorem stock_lower_acquire_selected_producer_block {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState)
      (bi producerIndex value producer : Nat) (block : Clif.Block) (stm : Clif.Stmt)
      (info : IInfo) (ty : Clif.Ty) (flags : Clif.MemFlags) (pointer : Nat),
      Backend.buildCtx f = .ok (original,ranges,initial) ∧ f.blocks[bi]? = some block ∧
      event.termInst = blockStart f bi+block.body.length ∧ block.body[producerIndex]? = some stm ∧
      producer = blockStart f bi+producerIndex ∧ stm.inst = .atomicLoad ty flags pointer ∧
      event.ctx.defInst? value = some producer ∧ event.ctx.insts[producer]? = some info ∧
      info.clif = some (.atomicLoad ty flags pointer) ∧ eTy ty = true ∧ flags.endianness ≠ some .big := by
  obtain ⟨original,ranges,initial,value,producer,info,ty,flags,pointer,built,defined,installed,source,
    integer,little,producerSource,color⟩ := stock_lower_acquire_output_source_color run scope events records recorded emitted selectedId
  obtain ⟨other,otherRanges,otherInitial,bi,block,otherBuilt,blockAt,termEq,bounds⟩ :=
    stock_lower_record_output_block_colors run scope events records
  have equal := Except.ok.inj (built.symm.trans otherBuilt)
  have ctxEq : original = other := congrArg Prod.fst equal
  have rangesEq : ranges = otherRanges := congrArg (fun pair => pair.2.1) equal
  rw [← ctxEq,← rangesEq] at bounds
  have interval := bounds _ color
  have member := source_event_same_block_of_color built blockAt producerSource interval.1 interval.2
  rcases (block_color_events_member built bi block blockAt producer).mp member with body | terminal
  · obtain ⟨stm,j,statement,effect,position⟩ := body
    obtain ⟨actualInfo,present,actualSource,results⟩ := (ctxSpec_of built).facts.stmt bi block j stm blockAt statement
    have view := stock_lower_event_build_source_slots run scope events built
    have current : event.ctx.insts[producer]? = some actualInfo := by
      rw [position]
      exact view _ actualInfo stm.inst present actualSource
    have infoEq := Option.some.inj (current.symm.trans installed)
    have instEq : stm.inst = .atomicLoad ty flags pointer :=
      Option.some.inj (actualSource.symm.trans (congrArg IInfo.clif infoEq).trans source)
    exact ⟨original,ranges,initial,bi,j,value,producer,block,stm,info,ty,flags,pointer,
      built,blockAt,termEq,statement,position,instEq,defined,installed,source,integer,little⟩
  · have same : producer = event.termInst := terminal.trans termEq.symm
    have noSource := stock_lower_event_term_source_none run events
    have actual : event.ctx.insts[event.termInst]!.clif = some (.atomicLoad ty flags pointer) := by
      rw [← same]
      simp only [getElem!_def,installed,Option.getD_some,source]
    rw [noSource] at actual
    cases actual

end Backend.Stock.Proof.Acquire810
