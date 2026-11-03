import FV.Backend.Proof.StockAcquireOriginalIntervalFrames

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Original admission and actual block execution internally construct both deferred source boundaries. -/
theorem stock_lower_acquire_positioned_source_memory {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (block : Clif.Block) (producerIndex consumerIndex value producer : Nat)
      (producerStmt consumerStmt : Clif.Stmt) (ty target : Clif.Ty) (flags : Clif.MemFlags) (pointer : Nat),
      f.blocks[event.block]? = some block ∧ block.body[producerIndex]? = some producerStmt ∧
      block.body[consumerIndex]? = some consumerStmt ∧ producerIndex < consumerIndex ∧
      producer = blockStart f event.block+producerIndex ∧ record.inst = blockStart f event.block+consumerIndex ∧
      producerStmt.inst = .atomicLoad ty flags pointer ∧ consumerStmt.inst = .extend .uextend target value ∧
      eTy ty = true ∧ flags.endianness ≠ some .big ∧ target.width ≤ 64 ∧
      ∀ (env : Clif.Env) (fuel : Nat) (s : Clif.State) (values : List Clif.Val) (memory : Clif.Mem),
        s.frame.body = block.body → Clif.runLoop env {funcs := []} fuel s = .returned values memory →
        ∃ (atProducer atConsumer : Clif.State) (producerFuel consumerFuel : Nat),
          producerFuel+producerIndex = fuel ∧ consumerFuel+(consumerIndex-producerIndex) = producerFuel ∧
          atProducer.frame.body = block.body.drop producerIndex ∧ atConsumer.frame.body = block.body.drop consumerIndex ∧
          Clif.runLoop env {funcs := []} producerFuel atProducer = .returned values memory ∧
          Clif.runLoop env {funcs := []} consumerFuel atConsumer = .returned values memory ∧
          SourceSteps (SourceInstResult env {funcs := []} event.ctx)
            (List.range' (blockStart f event.block) producerIndex) (s.frame,s.mem) (atProducer.frame,atProducer.mem) ∧
          SourceSteps (SourceInstResult env {funcs := []} event.ctx)
            (List.range' producer (consumerIndex-producerIndex))
            (atProducer.frame,atProducer.mem) (atConsumer.frame,atConsumer.mem) ∧
          atConsumer.mem = atProducer.mem := by
  obtain ⟨original,ranges,initial,block,producerIndex,consumerIndex,value,producer,producerStmt,consumerStmt,
    info,rootInfo,ty,target,flags,pointer,built,blockAt,producerAt,consumerAt,position,current,before,
    atomic,extension,valueResult,defined,installed,source,rootInstalled,rootSource,integer,little,fits⟩ :=
    stock_lower_acquire_selected_source_endpoints run scope dominated events records recorded emitted selectedId
  obtain ⟨positive,color⟩ := stock_lower_acquire_original_definition_color run scope events records recorded emitted selectedId
    rootInstalled rootSource defined
  have frames := stock_lower_record_original_interval_frames run scope events records built positive color
  have view := stock_lower_event_build_source_slots run scope events built
  have slots : ∀ j stm,block.body[j]? = some stm →
      ∃ actualInfo,event.ctx.insts[blockStart f event.block+j]? = some actualInfo ∧
        actualInfo.clif = some stm.inst ∧ actualInfo.results = stm.results := by
    intro j stm statement
    obtain ⟨actualInfo,present,actualSource,results⟩ := (ctxSpec_of built).facts.stmt event.block block j stm blockAt statement
    exact ⟨actualInfo,view _ actualInfo stm.inst present actualSource,actualSource,results⟩
  have consumerBound := (List.getElem?_eq_some_iff.mp consumerAt).1
  have exactSlice : producerIndex+(consumerIndex-producerIndex) = consumerIndex := by omega
  refine ⟨block,producerIndex,consumerIndex,value,producer,producerStmt,consumerStmt,ty,target,flags,pointer,
    blockAt,producerAt,consumerAt,before,position,current,atomic,extension,integer,little,fits,?_⟩
  intro env fuel s values memory remaining returned
  have initialBody : s.frame.body = block.body.drop 0 := by simpa only [List.drop_zero] using remaining
  obtain ⟨atProducer,producerFuel,totalProducer,producerRun,producerBody,priorSteps⟩ :=
    bare_returned_source_slice slots producerIndex (start := 0) (by omega) initialBody returned
  simp only [Nat.zero_add,Nat.add_zero] at totalProducer producerBody priorSteps
  obtain ⟨atConsumer,consumerFuel,totalConsumer,consumerRun,consumerBody,sliceSteps⟩ :=
    bare_returned_source_slice slots (consumerIndex-producerIndex) (by omega) producerBody producerRun
  rw [exactSlice] at consumerBody
  have reads : ∀ slot ∈ List.range' (blockStart f event.block+producerIndex) (consumerIndex-producerIndex),
      SourceReadFrame event.ctx slot := by
    intro slot member
    obtain ⟨offset,offsetBound,equal⟩ := List.mem_range'.mp member
    simp only [Nat.one_mul] at equal
    have statementBound : producerIndex+offset < block.body.length := by omega
    have statement : block.body[producerIndex+offset]? = some block.body[producerIndex+offset] :=
      List.getElem?_eq_getElem statementBound
    have read := frames event.block (producerIndex+offset) block block.body[producerIndex+offset] blockAt statement
      (by rw [position];omega) (by rw [current];omega)
    simpa only [equal,Nat.add_assoc] using read
  have memoryEq := source_steps_read_memory sliceSteps reads
  refine ⟨atProducer,atConsumer,producerFuel,consumerFuel,totalProducer,totalConsumer,
    producerBody,consumerBody,producerRun,consumerRun,priorSteps,?_,memoryEq⟩
  simpa only [position] using sliceSteps

end Backend.Stock.Proof.Acquire810
