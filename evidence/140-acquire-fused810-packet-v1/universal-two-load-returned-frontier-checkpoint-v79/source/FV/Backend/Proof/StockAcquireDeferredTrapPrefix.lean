import FV.Backend.Proof.StockAcquireDeferredReadPrefixRun

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A faulting deferred interval either faults at this producer or derives its successful read before the later fault. -/
theorem source_endpoint_deferred_trap_prefix {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record)
    {env : Clif.Env} {program : Clif.Program} {start : Clif.Frame × Clif.Mem} {code : Clif.TrapCode}
    (body : start.1.body = R.block.body.drop R.producerIndex)
    (failed : SourceTrapSteps (SourceInstResult env program event.ctx) (SourceInstFault env program event.ctx)
      (List.range' R.producer (R.consumerIndex-R.producerIndex)) start code) :
    SourceInstFault env program event.ctx R.producer start code ∨
    ∃ (front : List Nat) (slot : Nat) (suffix : List Nat) (atFault : Clif.Frame × Clif.Mem) (small : Clif.Val),
      List.range' R.producer (R.consumerIndex-R.producerIndex) = (R.producer::front)++slot::suffix ∧
      SourceSteps (SourceInstResult env program event.ctx) (R.producer::front) start atFault ∧
      SourceInstFault env program event.ctx slot atFault code ∧
      Clif.evalInst start.1 start.2 (.atomicLoad R.ty R.flags R.pointer) = .ok ([small],start.2) ∧
      atFault.1.regs R.value = some small ∧ atFault.1.regs R.pointer = start.1.regs R.pointer ∧
      atFault.1.slots = start.1.slots ∧ atFault.2 = start.2 := by
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
  have actualReads : ∀ slot ∈ List.range' R.producer (R.consumerIndex-R.producerIndex),SourceReadFrame event.ctx slot := by
    simpa only [R.position] using reads
  obtain ⟨front,slot,suffix,atFault,parts,executed,fault,memory⟩ := source_first_trap_read_memory failed actualReads
  have fullParts := parts
  have countEq : R.consumerIndex-R.producerIndex = (R.consumerIndex-R.producerIndex-1)+1 := by omega
  rw [countEq,List.range'_succ] at parts
  cases front with
  | nil =>
    simp only [List.nil_append] at parts
    have slotEq := (List.cons.inj parts).1.symm
    subst slot
    cases executed
    exact Or.inl fault
  | cons first front =>
    have firstEq := (List.cons.inj parts).1
    subst first
    have sourceSteps : SourceSteps (SourceInstResult env program event.ctx)
        ((blockStart f event.block+R.producerIndex)::front) start atFault := by
      simpa only [R.position] using executed
    have definedAt : event.ctx.defInst? R.value = some (blockStart f event.block+R.producerIndex) := by
      simpa only [R.position] using R.defined
    have installedAt : event.ctx.insts[blockStart f event.block+R.producerIndex]? = some R.info := by
      simpa only [R.position] using R.installed
    obtain ⟨small,atomic,loaded⟩ := source_atomic_loaded_prefix mapped dominated.ssa R.blockAt R.producerAt R.result
      definedAt installedAt R.source R.little body sourceSteps
    have pointer := available_source_prefix_pointer R.blockAt pointerAvailable body executed
    have slotsEq := source_steps_slots_frame executed
    exact Or.inr ⟨front,slot,suffix,atFault,small,fullParts,executed,fault,atomic,loaded,pointer,slotsEq,memory⟩

end Backend.Stock.Proof.Acquire810
