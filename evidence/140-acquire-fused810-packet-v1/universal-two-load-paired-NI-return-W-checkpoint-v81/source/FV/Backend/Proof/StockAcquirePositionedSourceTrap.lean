import FV.Backend.Proof.StockAcquirePositionedSourceMemory

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The actual first trap occurs before the producer, in its read slice, or after the consumer boundary. -/
def SourceBlockTrapPartition (ctx : Ctx) (block : Clif.Block) (base producerIndex consumerIndex : Nat)
    (env : Clif.Env) (fuel : Nat) (s : Clif.State) (code : Clif.TrapCode) : Prop :=
  SourceTrapSteps (SourceInstResult env {funcs := []} ctx) (SourceInstFault env {funcs := []} ctx)
      (List.range' base producerIndex) (s.frame,s.mem) code ∨
  ∃ (atProducer : Clif.State) (producerFuel : Nat),producerFuel+producerIndex = fuel ∧
    atProducer.frame.body = block.body.drop producerIndex ∧
    SourceSteps (SourceInstResult env {funcs := []} ctx) (List.range' base producerIndex)
      (s.frame,s.mem) (atProducer.frame,atProducer.mem) ∧
    Clif.runLoop env {funcs := []} producerFuel atProducer = .trapped code ∧
    ((∃ (front : List Nat) (slot : Nat) (suffix : List Nat) (atFault : Clif.Frame × Clif.Mem),
      List.range' (base+producerIndex) (consumerIndex-producerIndex) = front++slot::suffix ∧
      SourceSteps (SourceInstResult env {funcs := []} ctx) front (atProducer.frame,atProducer.mem) atFault ∧
      SourceInstFault env {funcs := []} ctx slot atFault code ∧ atFault.2 = atProducer.mem) ∨
    ∃ (atConsumer : Clif.State) (consumerFuel : Nat),consumerFuel+(consumerIndex-producerIndex) = producerFuel ∧
      atConsumer.frame.body = block.body.drop consumerIndex ∧
      SourceSteps (SourceInstResult env {funcs := []} ctx)
        (List.range' (base+producerIndex) (consumerIndex-producerIndex))
        (atProducer.frame,atProducer.mem) (atConsumer.frame,atConsumer.mem) ∧
      Clif.runLoop env {funcs := []} consumerFuel atConsumer = .trapped code ∧ atConsumer.mem = atProducer.mem)

/-- Actual original selection and trapped block execution internally derive the complete source fault partition. -/
theorem stock_lower_acquire_positioned_source_trap {f : Clif.Function} {result : Result}
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
      ∀ (env : Clif.Env) (fuel : Nat) (s : Clif.State) (code : Clif.TrapCode),
        s.frame.body = block.body → Clif.runLoop env {funcs := []} fuel s = .trapped code →
        SourceBlockTrapPartition event.ctx block (blockStart f event.block) producerIndex consumerIndex env fuel s code := by
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
  intro env fuel s code remaining trapped
  have initialBody : s.frame.body = block.body.drop 0 := by simpa only [List.drop_zero] using remaining
  rcases bare_trapped_source_slice slots producerIndex (start := 0) (by omega) initialBody trapped with early |
    ⟨atProducer,producerFuel,totalProducer,producerRun,producerBody,priorSteps⟩
  · exact Or.inl (by simpa only [Nat.add_zero] using early)
  · simp only [Nat.zero_add,Nat.add_zero] at totalProducer producerBody priorSteps
    refine Or.inr ⟨atProducer,producerFuel,totalProducer,producerBody,priorSteps,producerRun,?_⟩
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
    rcases bare_trapped_source_slice slots (consumerIndex-producerIndex) (by omega) producerBody producerRun with within |
      ⟨atConsumer,consumerFuel,totalConsumer,consumerRun,consumerBody,sliceSteps⟩
    · exact Or.inl (source_first_trap_read_memory within reads)
    · rw [exactSlice] at consumerBody
      exact Or.inr ⟨atConsumer,consumerFuel,totalConsumer,consumerBody,sliceSteps,consumerRun,
        source_steps_read_memory sliceSteps reads⟩

end Backend.Stock.Proof.Acquire810
