import FV.Backend.Proof.StockAcquireSourceConsumerResult

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Successful original block execution supplies the value executed by the actual retained acquire chunk. -/
theorem stock_lower_acquire_selected_chunk_value {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (R : SourceEndpointReceipt f event record) (pointerReg dest resultId key : Nat),
      event.ctx.valueReg? R.pointer = some (.vreg pointerReg .int) ∧
      R.rootInfo.results = [resultId] ∧ event.ctx.valueReg? resultId = some (.vreg key .int) ∧
      dest = record.input.base.nextVreg ∧
      record.output.emitted = #[.loadAcquire (CTy.ofClif R.ty) (.vreg dest .int) (.vreg pointerReg .int) R.flags] ∧
      step.results = [[.vreg dest .int]] ∧
      (result.final.alias[key]?).join = some dest ∧ aliasNum result.final.alias key = dest ∧
      ∀ (env : Clif.Env) (fuel : Nat) (s : Clif.State) (values : List Clif.Val) (memory : Clif.Mem),
        s.frame.body = R.block.body → Clif.runLoop env {funcs := []} fuel s = .returned values memory →
        ∃ (atProducer atConsumer : Clif.State) (small widened : Clif.Val),
          Clif.evalInst atProducer.frame atProducer.mem (.atomicLoad R.ty R.flags R.pointer) = .ok ([small],atProducer.mem) ∧
          Clif.evalInst atConsumer.frame atConsumer.mem (.extend .uextend R.target R.value) = .ok ([widened],atConsumer.mem) ∧
          atConsumer.mem = atProducer.mem ∧ atConsumer.frame.slots = atProducer.frame.slots ∧
          ∀ (F : BitVec 64 → Prop) (sb : Nat) (syms : String → Option Nat) (isem : Backend.Proof.Sem)
            (MR : MemRelT),MRStable F MR → MemRefines F sb syms isem → MemRelOk F sb syms f MR →
            FrameTyped event.ctx atProducer.frame → ∀ (regs : Nat → CV) (world : Arm.ArmState),
            ValueHeld event.ctx atConsumer.frame regs R.pointer → MR atConsumer.frame.slots atConsumer.mem world →
            ∃ nextRegs nextWorld,seqRun isem record.output.emitted.toList regs world = some (.fall nextRegs nextWorld) ∧
              VHolds widened (nextRegs dest) ∧ (∀ n,n ≠ dest → nextRegs n = regs n) ∧
              MR atConsumer.frame.slots atConsumer.mem nextWorld := by
  obtain ⟨R,pointerReg,dest,resultId,key,register,results,resultReg,fresh,code,resultRegisters,finalAlias,finalNum⟩ :=
    stock_lower_acquire_selected_chunk run scope dominated events records recorded emitted selectedId
  refine ⟨R,pointerReg,dest,resultId,key,register,results,resultReg,fresh,code,resultRegisters,finalAlias,finalNum,?_⟩
  intro env fuel s values memory body returned
  obtain ⟨atProducer,atConsumer,producerFuel,consumerFuel,small,totalProducer,totalConsumer,
    producerBody,consumerBody,producerRun,consumerRun,priorSteps,sliceSteps,atomic,valueBound,pointerKept,slotsKept,memorySame⟩ :=
    source_endpoint_values run scope dominated events records recorded emitted selectedId R env fuel s values memory body returned
  have consumerBound := (List.getElem?_eq_some_iff.mp R.consumerAt).1
  have stmtEq := (List.getElem?_eq_some_iff.mp R.consumerAt).2
  have head : atConsumer.frame.body = R.consumerStmt::R.block.body.drop (R.consumerIndex+1) := by
    rw [consumerBody,List.drop_eq_getElem_cons consumerBound,stmtEq]
  obtain ⟨widened,nextMem,extension⟩ := bare_returned_uextend head R.extension consumerRun
  obtain ⟨loaded,loadedAt,loadedWidth,extensionValues,extensionMemory⟩ := evalInst_uextend_ok extension
  rw [extensionMemory] at extension
  refine ⟨atProducer,atConsumer,small,widened,atomic,extension,memorySame,slotsKept,?_⟩
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
  simpa only [code] using executed

end Backend.Stock.Proof.Acquire810
