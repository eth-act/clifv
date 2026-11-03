import FV.Backend.Proof.StockAcquireSelectedChunk

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- An internal selected endpoint receipt supplies the same positioned values for later machine composition. -/
theorem source_endpoint_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810)
    (R : SourceEndpointReceipt f event record) :
      ∀ (env : Clif.Env) (fuel : Nat) (s : Clif.State) (values : List Clif.Val) (memory : Clif.Mem),
        s.frame.body = R.block.body → Clif.runLoop env {funcs := []} fuel s = .returned values memory →
        ∃ (atProducer atConsumer : Clif.State) (producerFuel consumerFuel : Nat) (small : Clif.Val),
          producerFuel+R.producerIndex = fuel ∧ consumerFuel+(R.consumerIndex-R.producerIndex) = producerFuel ∧
          atProducer.frame.body = R.block.body.drop R.producerIndex ∧
          atConsumer.frame.body = R.block.body.drop R.consumerIndex ∧
          Clif.runLoop env {funcs := []} producerFuel atProducer = .returned values memory ∧
          Clif.runLoop env {funcs := []} consumerFuel atConsumer = .returned values memory ∧
          SourceSteps (SourceInstResult env {funcs := []} event.ctx)
            (List.range' (blockStart f event.block) R.producerIndex) (s.frame,s.mem) (atProducer.frame,atProducer.mem) ∧
          SourceSteps (SourceInstResult env {funcs := []} event.ctx)
            (List.range' R.producer (R.consumerIndex-R.producerIndex))
            (atProducer.frame,atProducer.mem) (atConsumer.frame,atConsumer.mem) ∧
          Clif.evalInst atProducer.frame atProducer.mem (.atomicLoad R.ty R.flags R.pointer) =
            .ok ([small],atProducer.mem) ∧ atConsumer.frame.regs R.value = some small ∧
          atConsumer.frame.regs R.pointer = atProducer.frame.regs R.pointer ∧
          atConsumer.frame.slots = atProducer.frame.slots ∧ atConsumer.mem = atProducer.mem := by
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
  intro env fuel s values memory remaining returned
  have initialBody : s.frame.body = R.block.body.drop 0 := by simpa only [List.drop_zero] using remaining
  obtain ⟨atProducer,producerFuel,totalProducer,producerRun,producerBody,priorSteps⟩ :=
    bare_returned_source_slice slots R.producerIndex (start := 0) (by omega) initialBody returned
  simp only [Nat.zero_add,Nat.add_zero] at totalProducer producerBody priorSteps
  obtain ⟨atConsumer,consumerFuel,totalConsumer,consumerRun,consumerBody,sliceSteps⟩ :=
    bare_returned_source_slice slots (R.consumerIndex-R.producerIndex) (by omega) producerBody producerRun
  rw [exactSlice] at consumerBody
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
  refine ⟨atProducer,atConsumer,producerFuel,consumerFuel,small,totalProducer,totalConsumer,
    producerBody,consumerBody,producerRun,consumerRun,priorSteps,?_,executed,loaded,pointerEq,slotsEq,memoryEq⟩
  simpa only [R.position] using completeSteps

end Backend.Stock.Proof.Acquire810
