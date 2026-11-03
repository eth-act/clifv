import FV.Backend.Proof.StockAcquireDeferredTrapPrefix
import FV.Backend.Proof.StockAcquireEntryPrefixChunkRun

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A real retained acquire runs before a later source fault without executing its future consumer. -/
theorem stock_lower_acquire_selected_deferred_read_run {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (R : SourceEndpointReceipt f event record) (pointerReg dest label index : Nat) (block : VBlock),
      result.code.blocks[label]? = some block ∧
      SegAt block index [.loadAcquire (CTy.ofClif R.ty) (.vreg dest .int)
        (.vreg (aliasNum result.final.alias pointerReg) .int) R.flags] ∧
      ∀ (env : Clif.Env) (program : Clif.Program) (args : List Clif.Val)
        (start producer : Clif.Frame × Clif.Mem) (code : Clif.TrapCode),
        SourceEntry f args start.1 → start.1.body = R.block.body →
        SourceSteps (SourceInstResult env program event.ctx)
          (List.range' (blockStart f event.block) R.producerIndex) start producer →
        SourceTrapSteps (SourceInstResult env program event.ctx) (SourceInstFault env program event.ctx)
          (List.range' R.producer (R.consumerIndex-R.producerIndex)) producer code →
        SourceInstFault env program event.ctx R.producer producer code ∨
        ∃ (front : List Nat) (slot : Nat) (suffix : List Nat) (atFault : Clif.Frame × Clif.Mem) (small : Clif.Val),
          List.range' R.producer (R.consumerIndex-R.producerIndex) = (R.producer::front)++slot::suffix ∧
          SourceSteps (SourceInstResult env program event.ctx) (R.producer::front) producer atFault ∧
          SourceInstFault env program event.ctx slot atFault code ∧
          atFault.1.regs R.value = some small ∧ atFault.2 = producer.2 ∧
          ∀ (F : BitVec 64 → Prop) (sb : Nat) (syms : String → Option Nat) (isem : Backend.Proof.Sem)
            (MR : MemRelT),MRStable F MR → MemRefines F sb syms isem → MemRelOk F sb syms f MR →
            ∀ (regs : Nat → CV) (world : Arm.ArmState),
            ValueHeld event.ctx atFault.1 (fun n => regs (aliasNum result.final.alias n)) R.pointer →
            MR atFault.1.slots atFault.2 world →
            ∃ (raw : BitVec R.ty.width) (nextRegs : Nat → CV) (nextWorld : Arm.ArmState),
              small = ⟨R.ty,raw⟩ ∧
              seqRun isem [.loadAcquire (CTy.ofClif R.ty) (.vreg dest .int)
                (.vreg (aliasNum result.final.alias pointerReg) .int) R.flags] regs world = some (.fall nextRegs nextWorld) ∧
              nextRegs dest = ofX (raw.setWidth 64) ∧
              (∀ n,n ≠ dest → nextRegs n = regs n) ∧ MR atFault.1.slots atFault.2 nextWorld := by
  obtain ⟨R,pointerReg,dest,resultId,key,label,index,block,register,results,resultReg,fresh,terminal,finalAlias,finalNum,found,segment⟩ :=
    stock_lower_acquire_selected_resolved_segment run scope dominated events records recorded emitted selectedId
  refine ⟨R,pointerReg,dest,label,index,block,found,segment,?_⟩
  intro env program args start producer code entered body priorSteps failed
  have view := stock_lower_event_build_source_slots run scope events R.built
  have slots : ∀ j stm,R.block.body[j]? = some stm →
      ∃ info,event.ctx.insts[blockStart f event.block+j]? = some info ∧ info.clif = some stm.inst ∧ info.results = stm.results := by
    intro j stm statement
    obtain ⟨info,installed,source,results⟩ := (ctxSpec_of R.built).facts.stmt event.block R.block j stm R.blockAt statement
    exact ⟨info,view _ info stm.inst installed source,source,results⟩
  have initialBody : start.1.body = R.block.body.drop 0 := by simpa only [List.drop_zero] using body
  have producerBound := (List.getElem?_eq_some_iff.mp R.producerAt).1
  have actualSteps : SourceSteps (SourceInstResult env program event.ctx)
      (List.range' (blockStart f event.block+0) R.producerIndex) start producer := by
    simpa only [Nat.add_zero] using priorSteps
  have producerBody := source_steps_body_prefix slots (start := 0) (count := R.producerIndex)
    (by omega) initialBody actualSteps
  have function : start.1.func = f := by
    obtain ⟨block,regs,entry,argsTypes,paramTypes,bound,frame⟩ := entered
    rw [frame]
  have initialTyped := stock_lower_entered_frame_typed_frame run dominated events entered
  have typed := stock_lower_source_body_prefix_frame_typed run scope dominated events R.built R.blockAt
    (start := 0) (count := R.producerIndex) (by omega) initialBody function initialTyped actualSteps
  rcases source_endpoint_deferred_trap_prefix run scope dominated events records recorded emitted selectedId R
      (by simpa only [Nat.zero_add] using producerBody) failed with immediate |
      ⟨front,slot,suffix,atFault,small,parts,executed,fault,atomic,loaded,pointerKept,slotsKept,memorySame⟩
  · exact Or.inl immediate
  · refine Or.inr ⟨front,slot,suffix,atFault,small,parts,executed,fault,loaded,memorySame,?_⟩
    intro F sb syms isem MR stable memorySem memoryOk regs world held memoryRel
    obtain ⟨pointer,raw,pointerSource,valid,read,sourceValues,sourceMemory⟩ := evalInst_atomicLoad_inv R.little atomic
    have mapped := (stock_lower_record_context run scope events).1
    have pointerCtx := mapped.addr64 R.producer R.info _ R.pointer R.installed R.source rfl
    have pointerType : pointer.ty = .i64 := by
      have actualType := typed R.pointer (.int 64) pointer pointerCtx pointerSource
      have int64 : ∀ ty : Clif.Ty,CTy.ofClif ty = .int 64 → ty = .i64 := by
        intro ty
        cases ty <;> simp [CTy.ofClif]
      exact int64 pointer.ty actualType
    have pointerAtFault := pointerKept.trans pointerSource
    obtain ⟨actualReg,found,pointerHeld⟩ := held pointer pointerAtFault
    have regEq : actualReg = pointerReg := (Reg.vreg.inj (Option.some.inj (found.symm.trans register))).1
    subst actualReg
    exact acquire_deferred_read_prefix_run stable memorySem memoryOk R.integer R.little
      pointerSource pointerType pointerKept memorySame atomic pointerHeld memoryRel

end Backend.Stock.Proof.Acquire810
