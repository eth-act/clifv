import FV.Backend.Proof.StockAcquireSourceIndexedConsumer

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The actual resolved acquire executes from finite source history, including prefixes before later faults. -/
theorem stock_lower_acquire_source_prefix_chunk_run {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (R : SourceEndpointReceipt f event record) (pointerReg dest label index : Nat) (block : VBlock),
      result.code.blocks[label]? = some block ∧
      SegAt block index [.loadAcquire (CTy.ofClif R.ty) (.vreg dest .int)
        (.vreg (aliasNum result.final.alias pointerReg) .int) R.flags] ∧
      ∀ (env : Clif.Env) (program : Clif.Program) (start consumer after : Clif.Frame × Clif.Mem),
        start.1.body = R.block.body →
        SourceSteps (SourceInstResult env program event.ctx)
          (List.range' (blockStart f event.block) R.consumerIndex) start consumer →
        SourceInstResult env program event.ctx record.inst consumer after →
        ∃ (producer : Clif.Frame × Clif.Mem) (small widened : Clif.Val),
          Clif.evalInst producer.1 producer.2 (.atomicLoad R.ty R.flags R.pointer) = .ok ([small],producer.2) ∧
          Clif.evalInst consumer.1 consumer.2 (.extend .uextend R.target R.value) = .ok ([widened],consumer.2) ∧
          consumer.2 = producer.2 ∧ consumer.1.slots = producer.1.slots ∧
          ∀ (F : BitVec 64 → Prop) (sb : Nat) (syms : String → Option Nat) (isem : Backend.Proof.Sem)
            (MR : MemRelT),MRStable F MR → MemRefines F sb syms isem → MemRelOk F sb syms f MR →
            FrameTyped event.ctx producer.1 → ∀ (regs : Nat → CV) (world : Arm.ArmState),
            ValueHeld event.ctx consumer.1 (fun n => regs (aliasNum result.final.alias n)) R.pointer →
            MR consumer.1.slots consumer.2 world →
            ∃ nextRegs nextWorld,seqRun isem [.loadAcquire (CTy.ofClif R.ty) (.vreg dest .int)
              (.vreg (aliasNum result.final.alias pointerReg) .int) R.flags] regs world = some (.fall nextRegs nextWorld) ∧
              VHolds widened (nextRegs dest) ∧ (∀ n,n ≠ dest → nextRegs n = regs n) ∧ MR consumer.1.slots consumer.2 nextWorld := by
  obtain ⟨R,pointerReg,dest,resultId,key,label,index,block,register,results,resultReg,fresh,terminal,finalAlias,finalNum,found,segment⟩ :=
    stock_lower_acquire_selected_resolved_segment run scope dominated events records recorded emitted selectedId
  refine ⟨R,pointerReg,dest,label,index,block,found,segment,?_⟩
  intro env program start consumer after body prefixSteps consumerStep
  obtain ⟨producer,small,producerBody,consumerBody,priorSteps,sliceSteps,atomic,valueBound,pointerKept,slotsKept,memorySame⟩ :=
    source_endpoint_prefix_values run scope dominated events records recorded emitted selectedId R body prefixSteps
  obtain ⟨widened,extension⟩ := source_uextend_result_value R.rootInstalled R.rootSource consumerStep
  obtain ⟨loaded,loadedAt,width,extensionValues,extensionMemory⟩ := evalInst_uextend_ok extension
  rw [extensionMemory] at extension
  refine ⟨producer,small,widened,atomic,extension,memorySame,slotsKept,?_⟩
  intro F sb syms isem MR stable memorySem memoryOk typed regs world held memoryRel
  obtain ⟨pointer,raw,pointerSource,valid,read,sourceValues,sourceMemory⟩ := evalInst_atomicLoad_inv R.little atomic
  have pointerAtConsumer := pointerKept.trans pointerSource
  have mapped := (stock_lower_record_context run scope events).1
  have pointerCtx := mapped.addr64 R.producer R.info _ R.pointer R.installed R.source rfl
  have pointerType : pointer.ty = .i64 := by
    have actualType := typed R.pointer (.int 64) pointer pointerCtx pointerSource
    have int64 : ∀ ty : Clif.Ty,CTy.ofClif ty = .int 64 → ty = .i64 := by
      intro ty
      cases ty <;> simp [CTy.ofClif]
    exact int64 pointer.ty actualType
  obtain ⟨actualReg,found,pointerHeld⟩ := held pointer pointerAtConsumer
  have regEq : actualReg = pointerReg := (Reg.vreg.inj (Option.some.inj (found.symm.trans register))).1
  subst actualReg
  obtain ⟨nextRegs,nextWorld,same,executed,value,other,after⟩ := acquire_deferred_pair_run stable memorySem memoryOk
    R.integer R.fits R.little pointerSource pointerType pointerKept valueBound memorySame atomic extension pointerHeld memoryRel
  refine ⟨nextRegs,nextWorld,?_,value,other,after⟩
  exact executed

end Backend.Stock.Proof.Acquire810
