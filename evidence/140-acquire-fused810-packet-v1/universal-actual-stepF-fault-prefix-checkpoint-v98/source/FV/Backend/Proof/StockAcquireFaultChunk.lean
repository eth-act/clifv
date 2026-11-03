import FV.Backend.Proof.StockAcquireFaultFrontier

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- The actual final-alias chunk exposes the fault access from its derived pending frontier.
The pointer type and binding come from the existing relation; no source read succeeds at this point. -/
theorem stock_lower_acquire_fault_chunk {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (R : SourceEndpointReceipt f event record) (pointerReg dest : Nat),
      record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) =
        [.loadAcquire (CTy.ofClif R.ty) (.vreg dest .int) (.vreg pointerReg .int) R.flags] ∧
      ∀ (env : Clif.Env) (program : Clif.Program) (initial : Clif.State) (atFault : Clif.Frame × Clif.Mem)
        (mp : ArmFault.MemMap) (code : Clif.TrapCode),MapFaults mp env program initial →
        SourceInstFault env program event.ctx R.producer atFault code →
        ∀ (MR : MemRelT) (frontier : ReadEffectFrontier event.ctx env program) (regs : Nat → CV) (world : Arm.ArmState),
          SourceReadCaptures event.ctx env program (event.output.records.reverse.take R.producerIndex)
            (initial.frame,initial.mem) atFault frontier.history →
          PendingReadMarks frontier record.output.state → RetiredUndemanded frontier record.output.state →
          PendingGuardedScanRel f result event.ctx event.block env program MR frontier.history record.output.state
            (R.producerIndex,atFault) regs world →
          frontier.pending = [] ∧
          GuardedScanRel f result event.ctx event.block MR record.output.state (R.producerIndex,atFault) regs world ∧
          ∃ address bytes,AcquireAt (.loadAcquire (CTy.ofClif R.ty) (.vreg dest .int) (.vreg pointerReg .int) R.flags)
            [regs pointerReg] world code address bytes ∧ ∃ j < bytes,mp (address+BitVec.ofNat 64 j) = .none := by
  obtain ⟨R,pointerReg,dest,resultId,key,register,results,resultReg,fresh,chunk,resultRegisters,finalAlias,finalNum⟩ :=
    stock_lower_acquire_selected_chunk run scope dominated events records recorded emitted selectedId
  refine ⟨R,aliasNum result.final.alias pointerReg,aliasNum result.final.alias dest,?_,?_⟩
  · rw [chunk]
    change [MInst.loadAcquire (CTy.ofClif R.ty)
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg dest .int))
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1) (.vreg pointerReg .int)) R.flags] = _
    rw [resolve_vreg,resolve_vreg]
    rfl
  · intro env program initial atFault mp code faults failed MR frontier regs world history pending retired prior
    have empty := stock_lower_acquire_fault_pending_empty run scope events records recorded emitted selectedId R history pending
    have guarded := stock_lower_acquire_fault_guarded_recovery run scope events records recorded emitted selectedId R history pending retired prior
    have retained : ∀ captured ∈ frontier.history,captured.record ∈ event.output.records := by
      intro captured member
      exact List.mem_reverse.mp (List.mem_of_mem_take (history.record_membership captured member))
    have held := stock_lower_acquire_pending_pointer_at_prefix run scope dominated events records recorded emitted selectedId R
      (Nat.le_refl _) retained pending retired prior.2.2.2
    obtain ⟨pointer,foundPointer,flag,j,bound,unmapped⟩ := source_endpoint_atomic_fault_program_prefix R faults history.source_steps failed
    have pointerSource := get_regs foundPointer
    have available := stock_lower_acquire_pointer_available_at_prefix run scope dominated events records recorded emitted selectedId R (Nat.le_refl _)
    have mapped := (stock_lower_record_context run scope events).1
    have pointerCtx := mapped.addr64 R.producer R.info _ R.pointer R.installed R.source rfl
    have restrictedPointer : (restrict atFault.1 (availOf f (availIn f result.ctx) event.block R.producerIndex)).regs R.pointer = some pointer := by
      rw [restrict_regs_of_mem available]
      exact pointerSource
    have actualType := prior.2.1.2 R.pointer (.int 64) pointer pointerCtx restrictedPointer
    have int64 : ∀ ty : Clif.Ty,CTy.ofClif ty = .int 64 → ty = .i64 := by intro ty;cases ty <;> simp [CTy.ofClif]
    have pointerType := int64 pointer.ty actualType
    obtain ⟨actualReg,present,pointerHeld⟩ := held pointer pointerSource
    have same : actualReg = pointerReg := (Reg.vreg.inj (Option.some.inj (present.symm.trans register))).1
    subst actualReg
    have address : lo64 (regs (aliasNum result.final.alias pointerReg)) = BitVec.ofNat 64 (Clif.effAddr pointer 0) :=
      (lo64_of_holds pointerHeld pointerType).trans (effAddr_zero pointer).symm
    refine ⟨empty,guarded,lo64 (regs (aliasNum result.final.alias pointerReg)),(CTy.ofClif R.ty).bytes,
      AcquireAt.acquire (atomTy_ofClif R.integer) flag,j,?_,?_⟩
    · have bytes : (CTy.ofClif R.ty).bytes = R.ty.bytes := by cases R.ty <;> rfl
      rw [bytes];exact bound
    · rw [address];exact unmapped

end Backend.Stock.Proof.Acquire810
