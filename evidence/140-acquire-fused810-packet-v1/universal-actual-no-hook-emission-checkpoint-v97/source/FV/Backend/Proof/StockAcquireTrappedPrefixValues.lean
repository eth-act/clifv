import FV.Backend.Proof.StockAcquireSourcePrefixValues

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual trapped execution either faults before the consumer or derives its finite successful prefix internally. -/
theorem stock_lower_acquire_trapped_prefix_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ R : SourceEndpointReceipt f event record,∀ (env : Clif.Env) (fuel : Nat) (s : Clif.State) (code : Clif.TrapCode),
      s.frame.body = R.block.body → Clif.runLoop env {funcs := []} fuel s = .trapped code →
      SourceTrapSteps (SourceInstResult env {funcs := []} event.ctx) (SourceInstFault env {funcs := []} event.ctx)
        (List.range' (blockStart f event.block) R.consumerIndex) (s.frame,s.mem) code ∨
      ∃ (producer : Clif.Frame × Clif.Mem) (consumer : Clif.State) (remaining : Nat) (small : Clif.Val),
        remaining+R.consumerIndex = fuel ∧ consumer.frame.body = R.block.body.drop R.consumerIndex ∧
        Clif.runLoop env {funcs := []} remaining consumer = .trapped code ∧
        SourceSteps (SourceInstResult env {funcs := []} event.ctx)
          (List.range' (blockStart f event.block) R.consumerIndex) (s.frame,s.mem) (consumer.frame,consumer.mem) ∧
        Clif.evalInst producer.1 producer.2 (.atomicLoad R.ty R.flags R.pointer) = .ok ([small],producer.2) ∧
        consumer.frame.regs R.value = some small ∧ consumer.frame.regs R.pointer = producer.1.regs R.pointer ∧
        consumer.frame.slots = producer.1.slots ∧ consumer.mem = producer.2 := by
  obtain ⟨R⟩ := stock_lower_acquire_source_endpoint_receipt run scope dominated events records recorded emitted selectedId
  have view := stock_lower_event_build_source_slots run scope events R.built
  have slots : ∀ j stm,R.block.body[j]? = some stm →
      ∃ info,event.ctx.insts[blockStart f event.block+j]? = some info ∧ info.clif = some stm.inst ∧ info.results = stm.results := by
    intro j stm statement
    obtain ⟨info,installed,source,results⟩ := (ctxSpec_of R.built).facts.stmt event.block R.block j stm R.blockAt statement
    exact ⟨info,view _ info stm.inst installed source,source,results⟩
  have inside := (List.getElem?_eq_some_iff.mp R.consumerAt).1
  refine ⟨R,?_⟩
  intro env fuel s code body trapped
  have initialBody : s.frame.body = R.block.body.drop 0 := by simpa only [List.drop_zero] using body
  rcases bare_trapped_source_slice slots R.consumerIndex (start := 0) (by omega) initialBody trapped with early |
    ⟨consumer,remaining,total,residual,consumerBody,prefixSteps⟩
  · exact Or.inl (by simpa only [Nat.add_zero] using early)
  · have actualPrefix : SourceSteps (SourceInstResult env {funcs := []} event.ctx)
        (List.range' (blockStart f event.block) R.consumerIndex) (s.frame,s.mem) (consumer.frame,consumer.mem) := by
      simpa only [Nat.add_zero] using prefixSteps
    obtain ⟨producer,small,producerBody,consumerBody',priorSteps,sliceSteps,atomic,loaded,pointer,slotsEq,memory⟩ :=
      source_endpoint_prefix_values run scope dominated events records recorded emitted selectedId R body actualPrefix
    exact Or.inr ⟨producer,consumer,remaining,small,total,by simpa only [Nat.zero_add] using consumerBody,
      residual,actualPrefix,atomic,loaded,pointer,slotsEq,memory⟩

end Backend.Stock.Proof.Acquire810
