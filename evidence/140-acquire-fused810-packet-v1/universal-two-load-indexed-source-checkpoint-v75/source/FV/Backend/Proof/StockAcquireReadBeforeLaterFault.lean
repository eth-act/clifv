import FV.Backend.Proof.StockAcquireReadPrefixWorld

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- An earlier actual acquire executes and retires its successful read before a later original source fault.
The consumer's source instruction does not execute. The fault frame and all source history stay fixed. -/
theorem stock_lower_acquire_read_before_later_fault {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ R : SourceEndpointReceipt f event record,
      ∀ (env : Clif.Env) (program : Clif.Program) (entry atFault : Clif.Frame × Clif.Mem)
        (cut : Nat) (code : Clif.TrapCode),entry.1.body = R.block.body →
        R.producerIndex < cut → cut ≤ R.consumerIndex →
        SourceInstFault env program event.ctx (blockStart f event.block+cut) atFault code →
        ∀ (F : BitVec 64 → Prop) (sb : Nat) (syms : String → Option Nat) (isem : Backend.Proof.Sem) (MR : MemRelT),
        MRStable F MR → MemRefines F sb syms isem → MemRelOk F sb syms f MR →
        ∀ (frontier : ReadEffectFrontier event.ctx env program) (regs : Nat → CV) (world : Arm.ArmState),
          SourceReadCaptures event.ctx env program (event.output.records.reverse.take cut) entry atFault frontier.history →
          PendingReadMarks frontier record.output.state → RetiredReadUnmarked frontier record.output.state →
          RetiredUndemanded frontier record.output.state →
          PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history record.output.state (cut,atFault) regs world →
          ∃ (captured : SunkReadSnapshot event.ctx env program) (remaining : List (SunkReadSnapshot event.ctx env program))
            (head : frontier.pending = captured::remaining) (nextRegs : Nat → CV) (nextWorld : Arm.ArmState),
            captured.record.inst = R.producer ∧
            seqRun isem (record.output.emitted.toList.map
              (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs world =
              some (.fall nextRegs nextWorld) ∧ SameWorld F nextWorld world ∧
            SourceInstFault env program event.ctx (blockStart f event.block+cut) atFault code ∧
            PendingGuardedScanRel f result event.ctx event.block env program MR (frontier.retire captured remaining head).history
              record.input (cut,atFault) nextRegs nextWorld ∧
            PendingReadMarks (frontier.retire captured remaining head) record.input ∧
            RetiredReadUnmarked (frontier.retire captured remaining head) record.input ∧
            RetiredUndemanded (frontier.retire captured remaining head) record.input := by
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
  intro env program entry atFault cut code body producerBefore beforeConsumer failed F sb syms isem MR stable memorySem memoryOk
    frontier regs world history pending retiredMarks retiredValues prior
  obtain ⟨block,blockAt,indices⟩ := stock_lower_event_forward_source_indices run scope events
  have blockEq := Option.some.inj (blockAt.symm.trans R.blockAt)
  subst block
  have inside := (List.getElem?_eq_some_iff.mp R.consumerAt).1
  have prefixIndices : (event.output.records.reverse.take cut).map (·.inst) = List.range' (blockStart f event.block) cut := by
    rw [List.map_take,indices]
    exact List.take_range'_of_length_ge (by omega)
  have sourceSteps := history.source_steps
  rw [prefixIndices] at sourceSteps
  obtain ⟨producer,small,producerBody,faultBody,priorSteps,sliceSteps,atomic,loaded,pointerKept,slotsKept,memorySame⟩ :=
    source_endpoint_partial_prefix_values run scope dominated events records recorded emitted selectedId R
      producerBefore beforeConsumer body sourceSteps
  have retained : ∀ captured ∈ frontier.history,captured.record ∈ event.output.records := by
    intro captured member
    exact List.mem_reverse.mp (List.mem_of_mem_take (history.record_membership captured member))
  have held := stock_lower_acquire_pending_pointer_at_prefix run scope dominated events records recorded emitted selectedId R
    (Nat.le_of_lt producerBefore) retained pending retiredValues prior.2.2.2
  obtain ⟨pointer,raw,pointerSource,valid,read,sourceValues,sourceMemory⟩ := evalInst_atomicLoad_inv R.little atomic
  have pointerAtFault := pointerKept.trans pointerSource
  have available := stock_lower_acquire_pointer_available_at_prefix run scope dominated events records recorded emitted selectedId R
    (Nat.le_of_lt producerBefore)
  have mapped := (stock_lower_record_context run scope events).1
  have pointerCtx := mapped.addr64 R.producer R.info _ R.pointer R.installed R.source rfl
  have restrictedPointer : (restrict atFault.1 (availOf f (availIn f result.ctx) event.block cut)).regs R.pointer = some pointer := by
    rw [restrict_regs_of_mem available]
    exact pointerAtFault
  have actualType := prior.2.1.2 R.pointer (.int 64) pointer pointerCtx restrictedPointer
  have int64 : ∀ ty : Clif.Ty,CTy.ofClif ty = .int 64 → ty = .i64 := by intro ty;cases ty <;> simp [CTy.ofClif]
  have pointerType := int64 pointer.ty actualType
  obtain ⟨actualReg,found,pointerHeld⟩ := held pointer pointerAtFault
  have regEq : actualReg = pointerReg := (Reg.vreg.inj (Option.some.inj (found.symm.trans register))).1
  subst actualReg
  obtain ⟨bits,nextRegs,nextWorld,smallEq,executed,value,other,memoryAfter,same⟩ :=
    acquire_deferred_read_prefix_run_world stable memorySem memoryOk R.integer R.little pointerSource pointerType
      pointerKept memorySame atomic pointerHeld prior.2.2.1
  have actualExecution : seqRun isem (record.output.emitted.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs world =
      some (.fall nextRegs nextWorld) := by rw [codeEq];exact executed
  have post := stock_lower_pending_frozen_source_frame run scope dominated events records R.blockAt R.consumerAt R.current
    recorded emitted stable beforeConsumer prior
    (stock_lower_acquire_resolved_defs run scope dominated events records recorded emitted selectedId) actualExecution same
  obtain ⟨captured,remaining,head,producerEq,member,recordMember⟩ := stock_lower_acquire_partial_prefix_head run scope events records
    recorded emitted selectedId R producerBefore beforeConsumer history pending retiredMarks
  have unique := stock_lower_actual_prefix_capture_indices_nodup run events history
  rw [frontier.split,List.map_append,List.nodup_append] at unique
  have pendingAfter := stock_lower_acquire_pending_marks_retire run scope events records recorded emitted selectedId R
    frontier captured remaining head producerEq unique.2.1 pending
  have retiredAfter := stock_lower_acquire_retired_marks run scope events records recorded emitted selectedId R
    frontier captured remaining head producerEq retiredMarks
  have valuesAfter := stock_lower_acquire_retired_undemanded run scope dominated events records recorded emitted selectedId R
    frontier captured remaining head producerEq retiredValues
  exact ⟨captured,remaining,head,nextRegs,nextWorld,producerEq,actualExecution,same,failed,post,pendingAfter,retiredAfter,valuesAfter⟩

end Backend.Stock.Proof.Acquire810
