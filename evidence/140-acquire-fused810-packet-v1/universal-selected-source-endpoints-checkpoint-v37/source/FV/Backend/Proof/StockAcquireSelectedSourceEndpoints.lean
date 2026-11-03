import FV.Backend.Proof.StockAcquireSelectedOriginalPair
import FV.Backend.Proof.StockAcquireSelectedTargetWidth

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- An internally derived atomic output color locates its exact original statement in the actual scan block. -/
theorem stock_lower_record_atomic_color_position {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {producer : Nat} {info : IInfo} {ty : Clif.Ty} {flags : Clif.MemFlags} {pointer : Nat}
    (installed : event.ctx.insts[producer]? = some info) (source : info.clif = some (.atomicLoad ty flags pointer))
    (positive : record.input.entryColor[producer]! ≠ 0)
    (outputColor : record.output.state.color = some record.input.entryColor[producer]!) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState) (bi j : Nat)
      (block : Clif.Block) (stm : Clif.Stmt),
      Backend.buildCtx f = .ok (original,ranges,initial) ∧ f.blocks[bi]? = some block ∧
      event.termInst = blockStart f bi+block.body.length ∧ block.body[j]? = some stm ∧
      producer = blockStart f bi+j ∧ stm.inst = .atomicLoad ty flags pointer := by
  obtain ⟨original,ranges,initial,built,func,table⟩ := stock_lower_record_color_events run events records
  have metadata : record.input.entryColor = (sourceMetadata original ranges).entryColor :=
    table.trans (sourceMetadata_color_events original ranges).symm
  rw [metadata] at positive outputColor
  have producerSource := source_color_positive_member original ranges producer positive
  have color := outputColor
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
    have actualAtomic : actualInfo.clif = some (.atomicLoad ty flags pointer) :=
      (congrArg IInfo.clif infoEq).trans source
    have instEq : stm.inst = .atomicLoad ty flags pointer :=
      Option.some.inj (actualSource.symm.trans actualAtomic)
    exact ⟨original,ranges,initial,bi,j,block,stm,built,blockAt,termEq,statement,position,instEq⟩
  · have same : producer = event.termInst := terminal.trans termEq.symm
    have noSource := stock_lower_event_term_source_none run events
    have actual : event.ctx.insts[event.termInst]!.clif = some (.atomicLoad ty flags pointer) := by
      rw [← same]
      simp only [getElem!_def,installed,Option.getD_some,source]
    rw [noSource] at actual
    cases actual


/-- Original dominance orders the actual atomic producer before its original extension consumer. -/
theorem stock_lower_acquire_selected_source_endpoints {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState) (block : Clif.Block)
      (producerIndex consumerIndex value producer : Nat) (producerStmt consumerStmt : Clif.Stmt)
      (info rootInfo : IInfo) (ty target : Clif.Ty) (flags : Clif.MemFlags) (pointer : Nat),
      Backend.buildCtx f = .ok (original,ranges,initial) ∧ f.blocks[event.block]? = some block ∧
      block.body[producerIndex]? = some producerStmt ∧ block.body[consumerIndex]? = some consumerStmt ∧
      producer = blockStart f event.block+producerIndex ∧ record.inst = blockStart f event.block+consumerIndex ∧
      producerIndex < consumerIndex ∧ producerStmt.inst = .atomicLoad ty flags pointer ∧
      consumerStmt.inst = .extend .uextend target value ∧ value ∈ producerStmt.results ∧
      event.ctx.defInst? value = some producer ∧ event.ctx.insts[producer]? = some info ∧
      info.clif = some (.atomicLoad ty flags pointer) ∧ event.ctx.insts[record.inst]? = some rootInfo ∧
      rootInfo.clif = some (.extend .uextend target value) ∧ eTy ty = true ∧
      flags.endianness ≠ some .big ∧ target.width ≤ 64 := by
  obtain ⟨rootInfo,target,value,producer,info,ty,flags,pointer,rootInstalled,rootSource,
    defined,installed,source,integer,little,positive,outputColor⟩ :=
    stock_lower_acquire_selected_original_pair run scope events records recorded emitted selectedId
  obtain ⟨original,ranges,initial,bi,producerIndex,block,producerStmt,built,blockAt,termEq,
    producerAt,position,atomic⟩ := stock_lower_record_atomic_color_position run scope events records installed source positive outputColor
  obtain ⟨consumerBlock,consumerIndex,consumerStmt,actualRoot,consumerBlockAt,consumerAt,current,consumerTerm,
    actualInstalled,actualSource⟩ := stock_lower_acquire_consumer_body_position run scope events records recorded emitted selectedId
  have blockIndex := source_block_terminal_unique blockAt consumerBlockAt (termEq.symm.trans consumerTerm)
  subst bi
  have blockEq := Option.some.inj (blockAt.symm.trans consumerBlockAt)
  subst consumerBlock
  have rootEq := Option.some.inj (actualInstalled.symm.trans rootInstalled)
  have consumerInst : consumerStmt.inst = .extend .uextend target value :=
    Option.some.inj (actualSource.symm.trans ((congrArg IInfo.clif rootEq).trans rootSource))
  obtain ⟨originalInfo,present,originalSource,results⟩ := (ctxSpec_of built).facts.stmt event.block block producerIndex producerStmt blockAt producerAt
  have view := stock_lower_event_build_source_slots run scope events built
  have actual : event.ctx.insts[producer]? = some originalInfo := by
    rw [position]
    exact view _ originalInfo producerStmt.inst present originalSource
  have infoEq := Option.some.inj (actual.symm.trans installed)
  obtain ⟨actualInfo,actualPresent,valueResult⟩ := (stock_lower_record_context run scope events).1.defInst value producer defined
  have actualEq := Option.some.inj (actualPresent.symm.trans installed)
  rw [actualEq,← infoEq,results] at valueResult
  have used : value ∈ Driver.instArgs consumerStmt.inst := by rw [consumerInst];simp only [Driver.instArgs,List.mem_singleton]
  have available := (dominated.uses original ranges initial built event.block block blockAt).1 consumerIndex consumerStmt consumerAt value used
  have future := ((mem_av blockAt).mp available).2
  have before : producerIndex < consumerIndex := by
    by_cases less : producerIndex < consumerIndex
    · exact less
    · exact False.elim (future ⟨producerIndex,producerStmt,by omega,producerAt,valueResult⟩)
  have fits := stock_lower_acquire_selected_target_width run scope events records rootInstalled rootSource recorded emitted selectedId
  exact ⟨original,ranges,initial,block,producerIndex,consumerIndex,value,producer,producerStmt,consumerStmt,
    info,rootInfo,ty,target,flags,pointer,built,blockAt,producerAt,consumerAt,position,current,before,atomic,consumerInst,
    valueResult,defined,installed,source,rootInstalled,rootSource,integer,little,fits⟩

end Backend.Stock.Proof.Acquire810
