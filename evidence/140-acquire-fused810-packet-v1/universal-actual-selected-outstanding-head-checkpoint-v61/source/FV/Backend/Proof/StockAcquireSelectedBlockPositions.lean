import FV.Backend.Proof.StockAcquireConsumerBodyPosition

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Distinct original blocks cannot share an allocated terminator slot. -/
theorem source_block_terminal_unique {f : Clif.Function} {first second : Nat}
    {left right : Clif.Block} (leftAt : f.blocks[first]? = some left) (rightAt : f.blocks[second]? = some right)
    (same : blockStart f first+left.body.length = blockStart f second+right.body.length) : first = second := by
  rcases Nat.lt_trichotomy first second with before | equal | after
  · have separated := block_layout_before f.blocks first second left leftAt before
    simp only [blockStart_eq] at same
    omega
  · exact equal
  · have separated := block_layout_before f.blocks second first right rightAt after
    simp only [blockStart_eq] at same
    omega

/-- Both real selected endpoints occupy original statements in the actual consumer block. -/
theorem stock_lower_acquire_selected_block_positions {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState) (block : Clif.Block)
      (producerIndex consumerIndex value producer : Nat) (producerStmt consumerStmt : Clif.Stmt)
      (info rootInfo : IInfo) (ty : Clif.Ty) (flags : Clif.MemFlags) (pointer : Nat),
      Backend.buildCtx f = .ok (original,ranges,initial) ∧ f.blocks[event.block]? = some block ∧
      block.body[producerIndex]? = some producerStmt ∧ block.body[consumerIndex]? = some consumerStmt ∧
      producer = blockStart f event.block+producerIndex ∧ record.inst = blockStart f event.block+consumerIndex ∧
      producerStmt.inst = .atomicLoad ty flags pointer ∧ value ∈ producerStmt.results ∧
      event.ctx.defInst? value = some producer ∧ event.ctx.insts[producer]? = some info ∧
      info.clif = some (.atomicLoad ty flags pointer) ∧ event.ctx.insts[record.inst]? = some rootInfo ∧
      rootInfo.clif = some consumerStmt.inst ∧ eTy ty = true ∧ flags.endianness ≠ some .big := by
  obtain ⟨original,ranges,initial,bi,producerIndex,value,producer,block,producerStmt,info,ty,flags,pointer,
    built,blockAt,termEq,producerAt,position,atomic,defined,installed,source,integer,little⟩ :=
    stock_lower_acquire_selected_producer_block run scope events records recorded emitted selectedId
  obtain ⟨consumerBlock,consumerIndex,consumerStmt,rootInfo,consumerBlockAt,consumerAt,current,consumerTerm,
    rootInstalled,rootSource⟩ := stock_lower_acquire_consumer_body_position run scope events records recorded emitted selectedId
  have blockIndex := source_block_terminal_unique blockAt consumerBlockAt (termEq.symm.trans consumerTerm)
  subst bi
  have blockEq := Option.some.inj (blockAt.symm.trans consumerBlockAt)
  subst consumerBlock
  obtain ⟨originalInfo,present,originalSource,results⟩ := (ctxSpec_of built).facts.stmt event.block block producerIndex producerStmt blockAt producerAt
  have view := stock_lower_event_build_source_slots run scope events built
  have actual : event.ctx.insts[producer]? = some originalInfo := by
    rw [position]
    exact view _ originalInfo producerStmt.inst present originalSource
  have infoEq := Option.some.inj (actual.symm.trans installed)
  obtain ⟨actualInfo,actualPresent,valueResult⟩ := (stock_lower_record_context run scope events).1.defInst value producer defined
  have actualEq := Option.some.inj (actualPresent.symm.trans installed)
  rw [actualEq,← infoEq,results] at valueResult
  exact ⟨original,ranges,initial,block,producerIndex,consumerIndex,value,producer,producerStmt,consumerStmt,
    info,rootInfo,ty,flags,pointer,built,blockAt,producerAt,consumerAt,position,current,atomic,valueResult,
    defined,installed,source,rootInstalled,rootSource,integer,little⟩

end Backend.Stock.Proof.Acquire810
