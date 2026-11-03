import FV.Backend.Proof.StockAcquireSelectedDeferredReadRun

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual trapped execution determines the producer prefix and its entire deferred interval internally. -/
theorem source_endpoint_bare_fault_partition {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord} (events : event ∈ result.blockScans.toList)
    (R : SourceEndpointReceipt f event record)
    {env : Clif.Env} {fuel : Nat} {start : Clif.State} {code : Clif.TrapCode}
    (body : start.frame.body = R.block.body) (trapped : Clif.runLoop env {funcs := []} fuel start = .trapped code) :
    SourceTrapSteps (SourceInstResult env {funcs := []} event.ctx) (SourceInstFault env {funcs := []} event.ctx)
      (List.range' (blockStart f event.block) R.producerIndex) (start.frame,start.mem) code ∨
    ∃ (producer : Clif.State) (remaining : Nat),remaining+R.producerIndex = fuel ∧
      producer.frame.body = R.block.body.drop R.producerIndex ∧
      Clif.runLoop env {funcs := []} remaining producer = .trapped code ∧
      SourceSteps (SourceInstResult env {funcs := []} event.ctx)
        (List.range' (blockStart f event.block) R.producerIndex) (start.frame,start.mem) (producer.frame,producer.mem) ∧
      (SourceTrapSteps (SourceInstResult env {funcs := []} event.ctx) (SourceInstFault env {funcs := []} event.ctx)
        (List.range' R.producer (R.consumerIndex-R.producerIndex)) (producer.frame,producer.mem) code ∨
      ∃ (consumer : Clif.State) (left : Nat),left+R.consumerIndex = fuel ∧
        consumer.frame.body = R.block.body.drop R.consumerIndex ∧
        Clif.runLoop env {funcs := []} left consumer = .trapped code ∧
        SourceSteps (SourceInstResult env {funcs := []} event.ctx)
          (List.range' R.producer (R.consumerIndex-R.producerIndex)) (producer.frame,producer.mem) (consumer.frame,consumer.mem)) := by
  have view := stock_lower_event_build_source_slots run scope events R.built
  have slots : ∀ j stm,R.block.body[j]? = some stm →
      ∃ info,event.ctx.insts[blockStart f event.block+j]? = some info ∧ info.clif = some stm.inst ∧ info.results = stm.results := by
    intro j stm statement
    obtain ⟨info,installed,source,results⟩ := (ctxSpec_of R.built).facts.stmt event.block R.block j stm R.blockAt statement
    exact ⟨info,view _ info stm.inst installed source,source,results⟩
  have producerBound := (List.getElem?_eq_some_iff.mp R.producerAt).1
  have consumerBound := (List.getElem?_eq_some_iff.mp R.consumerAt).1
  have before := R.before
  have initialBody : start.frame.body = R.block.body.drop 0 := by simpa only [List.drop_zero] using body
  rcases bare_trapped_source_slice slots R.producerIndex (start := 0) (by omega) initialBody trapped with early |
      ⟨producer,remaining,total,residual,producerBody,priorSteps⟩
  · exact Or.inl (by simpa only [Nat.add_zero] using early)
  · have actualBody : producer.frame.body = R.block.body.drop R.producerIndex := by
      simpa only [Nat.zero_add] using producerBody
    have actualPrior : SourceSteps (SourceInstResult env {funcs := []} event.ctx)
        (List.range' (blockStart f event.block) R.producerIndex) (start.frame,start.mem) (producer.frame,producer.mem) := by
      simpa only [Nat.add_zero] using priorSteps
    refine Or.inr ⟨producer,remaining,total,actualBody,residual,actualPrior,?_⟩
    rcases bare_trapped_source_slice slots (R.consumerIndex-R.producerIndex) (start := R.producerIndex)
        (by omega) actualBody residual with failed | ⟨consumer,left,leftTotal,consumerTrap,consumerBody,sliceSteps⟩
    · exact Or.inl (by simpa only [R.position] using failed)
    · refine Or.inr ⟨consumer,left,by omega,?_,consumerTrap,?_⟩
      · have position : R.producerIndex+(R.consumerIndex-R.producerIndex) = R.consumerIndex := by omega
        simpa only [position] using consumerBody
      · simpa only [R.position] using sliceSteps

end Backend.Stock.Proof.Acquire810
