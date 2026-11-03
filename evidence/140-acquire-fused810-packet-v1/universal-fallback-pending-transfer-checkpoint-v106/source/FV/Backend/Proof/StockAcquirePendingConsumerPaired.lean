import FV.Backend.Proof.StockAcquireConsumerSourceUpdate
import FV.Backend.Proof.StockAcquireDeferredRunPaired

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The actual consumer derives its pointer and memory relation from the pending driver invariant.
Original source history supplies the deferred read. The consumer preserves all remaining demanded bindings. -/
theorem stock_lower_acquire_pending_consumer_paired_transfer {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ R : SourceEndpointReceipt f event record,
      ∀ (env : Clif.Env) (program : Clif.Program) (start consumer after : Clif.Frame × Clif.Mem),
        start.1.body = R.block.body →
        SourceSteps (SourceInstResult env program event.ctx)
          (List.range' (blockStart f event.block) R.consumerIndex) start consumer →
        SourceInstResult env program event.ctx record.inst consumer after →
        ∀ (F Z : BitVec 64 → Prop) (sb : Nat) (syms : String → Option Nat) (isem : Backend.Proof.Sem) (MR : MemRelT),
        (∀ a,F a → Z a) → MRStable F MR → MemRefines F sb syms isem → MemRelOk F sb syms f MR →
        ∀ (frontier : ReadEffectFrontier event.ctx env program) (regs : Nat → CV) (world otherWorld : Arm.ArmState),
        (∀ captured ∈ frontier.history,captured.record ∈ event.output.records) →
        PendingReadMarks frontier record.output.state → RetiredUndemanded frontier record.output.state →
        PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history record.output.state
          (R.consumerIndex,consumer) regs world →
        PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history record.output.state
          (R.consumerIndex,consumer) regs otherWorld → SameWorld Z world otherWorld →
        ∃ nextRegs nextWorld nextOther,
          seqRun (E2E.pairSem isem) (record.output.emitted.toList.map
            (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
            regs (world,otherWorld) = some (.fall nextRegs (nextWorld,nextOther)) ∧
          PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history record.input
            (R.consumerIndex+1,after) nextRegs nextWorld ∧
          PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history record.input
            (R.consumerIndex+1,after) nextRegs nextOther ∧ SameWorld Z nextWorld nextOther := by
  obtain ⟨R,pointerReg,dest,resultId,key,register,results,resultReg,fresh,chunk,resultRegisters,finalAlias,finalNum⟩ :=
    stock_lower_acquire_selected_chunk run scope dominated events records recorded emitted selectedId
  have terminal := (stock_lower_freshAlias_terminal run (n := dest) (by
    rw [fresh]
    exact stock_lower_blockScanInitialFrontier run event events record records)).2
  have codeEq : record.output.emitted.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) =
      [MInst.loadAcquire (CTy.ofClif R.ty) (.vreg dest .int) (.vreg (aliasNum result.final.alias pointerReg) .int) R.flags] := by
    rw [chunk]
    change [MInst.loadAcquire (CTy.ofClif R.ty)
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg dest .int))
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg pointerReg .int)) R.flags] = _
    rw [resolve_vreg,resolve_vreg]
    change [MInst.loadAcquire (CTy.ofClif R.ty) (.vreg (aliasNum result.final.alias dest) .int)
      (.vreg (aliasNum result.final.alias pointerReg) .int) R.flags] = _
    rw [terminal]
  refine ⟨R,?_⟩
  intro env program start consumer after body prefixSteps consumerStep F Z sb syms isem MR frame stable memorySem memoryOk
    frontier regs world otherWorld retained marked retired related otherRelated worlds
  obtain ⟨func,dfg,memory,values⟩ := related
  obtain ⟨otherFunc,otherDFG,otherMemory,otherValues⟩ := otherRelated
  obtain ⟨producer,small,producerBody,consumerBody,priorSteps,sliceSteps,atomic,loaded,pointerKept,slotsKept,memorySame⟩ :=
    source_endpoint_prefix_values run scope dominated events records recorded emitted selectedId R body prefixSteps
  obtain ⟨widened,extension⟩ := source_uextend_result_value R.rootInstalled R.rootSource consumerStep
  obtain ⟨loadedValue,loadedAt,width,extensionValues,extensionMemory⟩ := evalInst_uextend_ok extension
  rw [extensionMemory] at extension
  have held := stock_lower_acquire_pending_pointer_held run scope dominated events records recorded emitted selectedId R
    retained marked retired values
  obtain ⟨pointer,raw,pointerSource,valid,read,sourceValues,sourceMemory⟩ := evalInst_atomicLoad_inv R.little atomic
  have pointerAtConsumer := pointerKept.trans pointerSource
  obtain ⟨otherProducer,otherInfo,otherTy,otherFlags,otherPointer,otherDefined,otherInstalled,otherSource,
    otherInteger,otherLittle,available⟩ := stock_lower_acquire_selected_pointer_available run scope dominated events records
      R.blockAt R.consumerAt R.current R.rootInstalled R.rootSource recorded emitted selectedId
  have producerEq := Option.some.inj (otherDefined.symm.trans R.defined)
  subst otherProducer
  have infoEq := Option.some.inj (otherInstalled.symm.trans R.installed)
  subst otherInfo
  have pointerEq := (Clif.Inst.atomicLoad.inj (Option.some.inj (otherSource.symm.trans R.source))).2.2
  rw [pointerEq] at available
  have mapped := (stock_lower_record_context run scope events).1
  have pointerCtx := mapped.addr64 R.producer R.info _ R.pointer R.installed R.source rfl
  have restrictedPointer : (restrict consumer.1 (availOf f (availIn f result.ctx) event.block R.consumerIndex)).regs R.pointer = some pointer := by
    rw [restrict_regs_of_mem available]
    exact pointerAtConsumer
  have actualType := dfg.2 R.pointer (.int 64) pointer pointerCtx restrictedPointer
  have int64 : ∀ ty : Clif.Ty,CTy.ofClif ty = .int 64 → ty = .i64 := by
    intro ty
    cases ty <;> simp [CTy.ofClif]
  have pointerType := int64 pointer.ty actualType
  obtain ⟨actualReg,found,pointerHeld⟩ := held pointer pointerAtConsumer
  have regEq : actualReg = pointerReg := (Reg.vreg.inj (Option.some.inj (found.symm.trans register))).1
  subst actualReg
  obtain ⟨nextRegs,nextWorld,nextOther,same,executed,value,other,afterMemory,afterOther,pairedWorlds⟩ := acquire_deferred_run_paired frame stable memorySem memoryOk
    R.integer R.fits R.little pointerSource pointerType pointerKept loaded memorySame atomic extension pointerHeld memory otherMemory worlds
  have pairedExecution : seqRun (E2E.pairSem isem) (record.output.emitted.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs (world,otherWorld) =
      some (.fall nextRegs (nextWorld,nextOther)) := by rw [codeEq];exact executed
  obtain ⟨actualExecution,otherExecution⟩ := E2E.StockAcquirePair.seqRun_paired_fall_projections pairedExecution
  have statementResults : R.consumerStmt.results = [resultId] := by
    rw [← source_endpoint_consumer_results run scope events R]
    exact results
  have postValues := stock_lower_pending_fresh_record_values run scope dominated events records
    R.blockAt R.consumerAt R.current R.rootInstalled R.rootSource results statementResults resultReg recorded emitted
    resultRegisters (by omega) values (stock_lower_acquire_resolved_defs run scope dominated events records recorded emitted selectedId)
    actualExecution value
  have otherPostValues := stock_lower_pending_fresh_record_values run scope dominated events records
    R.blockAt R.consumerAt R.current R.rootInstalled R.rootSource results statementResults resultReg recorded emitted
    resultRegisters (by omega) otherValues (stock_lower_acquire_resolved_defs run scope dominated events records recorded emitted selectedId)
    otherExecution value
  have sourceValue : instOutcome env program consumer.1 consumer.2 (.extend .uextend R.target R.value) =
      .ok ([widened],consumer.2) := extension
  obtain ⟨sourceMemory,sourceRegs⟩ := source_single_result_update R.rootInstalled R.rootSource results consumerStep sourceValue
  have actualPostValues := pending_values_frame_regs sourceRegs postValues
  have postDFG := stock_lower_source_step_dfg run scope dominated events R.blockAt R.consumerAt R.current func dfg consumerStep
  have slots : after.1.slots = consumer.1.slots := source_steps_slots_frame (.cons consumerStep (.nil after))
  refine ⟨nextRegs,nextWorld,nextOther,pairedExecution,?_,?_,pairedWorlds⟩
  · refine ⟨(source_inst_result_function consumerStep).trans func,postDFG,?_,actualPostValues⟩
    rw [slots,sourceMemory]
    exact afterMemory
  · refine ⟨(source_inst_result_function consumerStep).trans otherFunc,postDFG,?_,pending_values_frame_regs sourceRegs otherPostValues⟩
    rw [slots,sourceMemory]
    exact afterOther

end Backend.Stock.Proof.Acquire810
