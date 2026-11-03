import FV.Backend.Proof.StockAcquireSelectedResolvedSegment

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The actual final-alias code segment executes the value from the original deferred source interval. -/
theorem stock_lower_acquire_selected_resolved_value {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (R : SourceEndpointReceipt f event record) (pointerReg dest label index : Nat) (block : VBlock),
      result.code.blocks[label]? = some block ∧
      SegAt block index [.loadAcquire (CTy.ofClif R.ty) (.vreg dest .int)
        (.vreg (aliasNum result.final.alias pointerReg) .int) R.flags] ∧
      ∀ (env : Clif.Env) (fuel : Nat) (s : Clif.State) (values : List Clif.Val) (memory : Clif.Mem),
        s.frame.body = R.block.body → Clif.runLoop env {funcs := []} fuel s = .returned values memory →
        ∃ (atProducer atConsumer : Clif.State) (small widened : Clif.Val),
          Clif.evalInst atProducer.frame atProducer.mem (.atomicLoad R.ty R.flags R.pointer) = .ok ([small],atProducer.mem) ∧
          Clif.evalInst atConsumer.frame atConsumer.mem (.extend .uextend R.target R.value) = .ok ([widened],atConsumer.mem) ∧
          atConsumer.mem = atProducer.mem ∧ atConsumer.frame.slots = atProducer.frame.slots ∧
          ∀ (F : BitVec 64 → Prop) (sb : Nat) (syms : String → Option Nat) (isem : Backend.Proof.Sem)
            (MR : MemRelT),MRStable F MR → MemRefines F sb syms isem → MemRelOk F sb syms f MR →
            FrameTyped event.ctx atProducer.frame → ∀ (regs : Nat → CV) (world : Arm.ArmState),
            ValueHeld event.ctx atConsumer.frame (fun n => regs (aliasNum result.final.alias n)) R.pointer → MR atConsumer.frame.slots atConsumer.mem world →
            ∃ nextRegs nextWorld,seqRun isem [.loadAcquire (CTy.ofClif R.ty) (.vreg dest .int) (.vreg (aliasNum result.final.alias pointerReg) .int) R.flags] regs world = some (.fall nextRegs nextWorld) ∧
              VHolds widened (nextRegs dest) ∧ (∀ n,n ≠ dest → nextRegs n = regs n) ∧
              MR atConsumer.frame.slots atConsumer.mem nextWorld := by
  obtain ⟨R,pointerReg,dest,resultId,key,label,index,block,register,results,resultReg,fresh,terminal,finalAlias,finalNum,found,segment⟩ :=
    stock_lower_acquire_selected_resolved_segment run scope dominated events records recorded emitted selectedId
  refine ⟨R,pointerReg,dest,label,index,block,found,segment,?_⟩
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
  exact executed

end Backend.Stock.Proof.Acquire810
