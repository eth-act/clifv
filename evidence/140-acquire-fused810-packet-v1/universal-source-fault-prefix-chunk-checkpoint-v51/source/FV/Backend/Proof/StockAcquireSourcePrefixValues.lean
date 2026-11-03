import FV.Backend.Proof.StockAcquireSourcePrefixBoundary

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- An actual finite successful source prefix derives the delayed value and memory without a future return premise. -/
theorem source_endpoint_prefix_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record)
    {env : Clif.Env} {program : Clif.Program} {start consumer : Clif.Frame × Clif.Mem}
    (body : start.1.body = R.block.body)
    (steps : SourceSteps (SourceInstResult env program event.ctx)
      (List.range' (blockStart f event.block) R.consumerIndex) start consumer) :
    ∃ (producer : Clif.Frame × Clif.Mem) (small : Clif.Val),
      producer.1.body = R.block.body.drop R.producerIndex ∧ consumer.1.body = R.block.body.drop R.consumerIndex ∧
      SourceSteps (SourceInstResult env program event.ctx)
        (List.range' (blockStart f event.block) R.producerIndex) start producer ∧
      SourceSteps (SourceInstResult env program event.ctx)
        (List.range' R.producer (R.consumerIndex-R.producerIndex)) producer consumer ∧
      Clif.evalInst producer.1 producer.2 (.atomicLoad R.ty R.flags R.pointer) = .ok ([small],producer.2) ∧
      consumer.1.regs R.value = some small ∧ consumer.1.regs R.pointer = producer.1.regs R.pointer ∧
      consumer.1.slots = producer.1.slots ∧ consumer.2 = producer.2 := by
  have mapped := (stock_lower_record_context run scope events).1
  obtain ⟨positive,color⟩ := stock_lower_acquire_original_definition_color run scope events records recorded emitted selectedId
    R.rootInstalled R.rootSource R.defined
  have frames := stock_lower_record_original_interval_frames run scope events records R.built positive color
  have view := stock_lower_event_build_source_slots run scope events R.built
  have slots : ∀ j stm,R.block.body[j]? = some stm →
      ∃ actualInfo,event.ctx.insts[blockStart f event.block+j]? = some actualInfo ∧
        actualInfo.clif = some stm.inst ∧ actualInfo.results = stm.results := by
    intro j stm statement
    obtain ⟨actualInfo,present,actualSource,results⟩ := (ctxSpec_of R.built).facts.stmt event.block R.block j stm R.blockAt statement
    exact ⟨actualInfo,view _ actualInfo stm.inst present actualSource,actualSource,results⟩
  have consumerBound := (List.getElem?_eq_some_iff.mp R.consumerAt).1
  have producerBound := (List.getElem?_eq_some_iff.mp R.producerAt).1
  have before := R.before
  have exactSlice : R.producerIndex+(R.consumerIndex-R.producerIndex) = R.consumerIndex := by omega
  have pointerUsed : R.pointer ∈ Driver.instArgs R.producerStmt.inst := by rw [R.atomic];simp only [Driver.instArgs,List.mem_singleton]
  have pointerAvailable := (dominated.uses R.original R.ranges R.initial R.built event.block R.block R.blockAt).1
    R.producerIndex R.producerStmt R.producerAt R.pointer pointerUsed
  have splitIndices : List.range' (blockStart f event.block) R.consumerIndex =
      List.range' (blockStart f event.block) R.producerIndex ++
        List.range' (blockStart f event.block+R.producerIndex) (R.consumerIndex-R.producerIndex) := by
    apply List.range'_eq_append_iff.mpr
    exact ⟨R.producerIndex,by omega,rfl,by simp⟩
  have splitSteps := steps
  rw [splitIndices] at splitSteps
  obtain ⟨producer,priorSteps,sliceSteps⟩ := source_steps_append_split splitSteps
  have initialBody : start.1.body = R.block.body.drop 0 := by simpa only [List.drop_zero] using body
  have producerBody : producer.1.body = R.block.body.drop R.producerIndex := by
    simpa only [Nat.add_zero,Nat.zero_add] using source_steps_body_prefix slots (start := 0)
      (count := R.producerIndex) (by omega) initialBody (by simpa only [Nat.add_zero] using priorSteps)
  have consumerBody : consumer.1.body = R.block.body.drop R.consumerIndex := by
    simpa only [Nat.add_zero,Nat.zero_add] using source_steps_body_prefix slots (start := 0)
      (count := R.consumerIndex) (by omega) initialBody (by simpa only [Nat.add_zero] using steps)
  have completeSteps := sliceSteps
  have reads : ∀ slot ∈ List.range' (blockStart f event.block+R.producerIndex) (R.consumerIndex-R.producerIndex),
      SourceReadFrame event.ctx slot := by
    intro slot member
    obtain ⟨offset,offsetBound,equal⟩ := List.mem_range'.mp member
    simp only [Nat.one_mul] at equal
    have statementBound : R.producerIndex+offset < R.block.body.length := by omega
    have statement : R.block.body[R.producerIndex+offset]? = some R.block.body[R.producerIndex+offset] :=
      List.getElem?_eq_getElem statementBound
    have read := frames event.block (R.producerIndex+offset) R.block R.block.body[R.producerIndex+offset] R.blockAt statement
      (by rw [R.position];omega) (by rw [R.current];omega)
    simpa only [equal,Nat.add_assoc] using read
  have memoryEq := source_steps_read_memory sliceSteps reads
  have pointerEq := available_source_prefix_pointer R.blockAt pointerAvailable producerBody completeSteps
  have slotsEq := source_steps_slots_frame completeSteps
  have countEq : R.consumerIndex-R.producerIndex = (R.consumerIndex-R.producerIndex-1)+1 := by omega
  rw [countEq,List.range'_succ] at sliceSteps
  have definedAt : event.ctx.defInst? R.value = some (blockStart f event.block+R.producerIndex) := by
    simpa only [R.position] using R.defined
  have installedAt : event.ctx.insts[blockStart f event.block+R.producerIndex]? = some R.info := by
    simpa only [R.position] using R.installed
  obtain ⟨small,executed,loaded⟩ := source_atomic_loaded_prefix mapped dominated.ssa R.blockAt R.producerAt R.result
    definedAt installedAt R.source R.little producerBody sliceSteps
  refine ⟨producer,small,producerBody,consumerBody,priorSteps,?_,executed,loaded,pointerEq,slotsEq,memoryEq⟩
  simpa only [R.position] using completeSteps

end Backend.Stock.Proof.Acquire810
