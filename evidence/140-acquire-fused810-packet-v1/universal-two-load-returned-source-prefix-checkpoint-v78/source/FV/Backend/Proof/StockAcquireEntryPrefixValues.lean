import FV.Backend.Proof.StockAcquireSourcePrefixFrameTyped

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Original source entry and actual finite history derive producer typing with the delayed values. -/
theorem source_endpoint_entry_prefix_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record)
    {env : Clif.Env} {program : Clif.Program} {args : List Clif.Val} {start consumer : Clif.Frame × Clif.Mem}
    (entered : SourceEntry f args start.1) (body : start.1.body = R.block.body)
    (steps : SourceSteps (SourceInstResult env program event.ctx)
      (List.range' (blockStart f event.block) R.consumerIndex) start consumer) :
    ∃ (producer : Clif.Frame × Clif.Mem) (small : Clif.Val),
      FrameTyped event.ctx producer.1 ∧
      Clif.evalInst producer.1 producer.2 (.atomicLoad R.ty R.flags R.pointer) = .ok ([small],producer.2) ∧
      consumer.1.regs R.value = some small ∧ consumer.1.regs R.pointer = producer.1.regs R.pointer ∧
      consumer.1.slots = producer.1.slots ∧ consumer.2 = producer.2 := by
  obtain ⟨producer,small,producerBody,consumerBody,priorSteps,sliceSteps,atomic,loaded,pointer,slots,memory⟩ :=
    source_endpoint_prefix_values run scope dominated events records recorded emitted selectedId R body steps
  have initialTyped := stock_lower_entered_frame_typed_frame run dominated events entered
  have function : start.1.func = f := by
    obtain ⟨block,regs,entry,argsTypes,paramTypes,bound,frame⟩ := entered
    rw [frame]
  have initialBody : start.1.body = R.block.body.drop 0 := by simpa only [List.drop_zero] using body
  have producerBound := (List.getElem?_eq_some_iff.mp R.producerAt).1
  have priorExecution : SourceSteps (SourceInstResult env program event.ctx)
      (List.range' (blockStart f event.block+0) R.producerIndex) start producer := by
    simpa only [Nat.add_zero] using priorSteps
  have typed := stock_lower_source_body_prefix_frame_typed run scope dominated events R.built R.blockAt
    (start := 0) (count := R.producerIndex) (by omega) initialBody function initialTyped priorExecution
  exact ⟨producer,small,typed,atomic,loaded,pointer,slots,memory⟩

end Backend.Stock.Proof.Acquire810
