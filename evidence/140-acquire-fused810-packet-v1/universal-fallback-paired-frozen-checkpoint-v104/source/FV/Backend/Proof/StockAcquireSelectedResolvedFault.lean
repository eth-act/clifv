import FV.Backend.Proof.StockAcquireSelectedResolvedValue

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- The actual final-alias code segment retains the exact original fault address and code. -/
theorem stock_lower_acquire_selected_resolved_fault {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (R : SourceEndpointReceipt f event record) (pointerReg dest label index : Nat) (block : VBlock),
      result.code.blocks[label]? = some block ∧
      SegAt block index [.loadAcquire (CTy.ofClif R.ty) (.vreg dest .int)
        (.vreg (aliasNum result.final.alias pointerReg) .int) R.flags] ∧
      ∀ (env : Clif.Env) (initial atFault : Clif.State) (mp : ArmFault.MemMap) (code : Clif.TrapCode),
        MapFaults mp env {funcs := []} initial → Reach env {funcs := []} initial atFault →
        SourceInstFault env {funcs := []} event.ctx R.producer (atFault.frame,atFault.mem) code →
        FrameTyped event.ctx atFault.frame → ∀ (regs : Nat → CV) (world : Arm.ArmState),
        ValueHeld event.ctx atFault.frame (fun n => regs (aliasNum result.final.alias n)) R.pointer →
        ∃ address bytes,AcquireAt (block.insts[index]!) [regs (aliasNum result.final.alias pointerReg)] world code address bytes ∧
          ∃ j < bytes,mp (address+BitVec.ofNat 64 j) = .none := by
  obtain ⟨R,pointerReg,dest,resultId,key,label,index,block,register,results,resultReg,fresh,terminal,finalAlias,finalNum,foundBlock,segment⟩ :=
    stock_lower_acquire_selected_resolved_segment run scope dominated events records recorded emitted selectedId
  refine ⟨R,pointerReg,dest,label,index,block,foundBlock,segment,?_⟩
  intro env initial atFault mp code faults reachable failed typed regs world held
  obtain ⟨pointer,found,flag,j,bound,unmapped⟩ := source_endpoint_atomic_fault R faults reachable failed
  have pointerSource := get_regs found
  have mapped := (stock_lower_record_context run scope events).1
  have pointerCtx := mapped.addr64 R.producer R.info _ R.pointer R.installed R.source rfl
  have actualType := typed R.pointer (.int 64) pointer pointerCtx pointerSource
  have int64 : ∀ ty : Clif.Ty,CTy.ofClif ty = .int 64 → ty = .i64 := by
    intro ty
    cases ty <;> simp [CTy.ofClif]
  have pointerType := int64 pointer.ty actualType
  obtain ⟨actualReg,present,pointerHeld⟩ := held pointer pointerSource
  have same : actualReg = pointerReg := (Reg.vreg.inj (Option.some.inj (present.symm.trans register))).1
  subst actualReg
  have address : lo64 (regs (aliasNum result.final.alias pointerReg)) = BitVec.ofNat 64 (Clif.effAddr pointer 0) :=
    (lo64_of_holds pointerHeld pointerType).trans (effAddr_zero pointer).symm
  refine ⟨lo64 (regs (aliasNum result.final.alias pointerReg)),(CTy.ofClif R.ty).bytes,?_,j,?_,?_⟩
  · have located := segment.head
    rw [getElem!_def,located]
    exact AcquireAt.acquire (atomTy_ofClif R.integer) flag
  · have bytes : (CTy.ofClif R.ty).bytes = R.ty.bytes := by cases R.ty <;> rfl
    rw [bytes]
    exact bound
  · rw [address]
    exact unmapped

end Backend.Stock.Proof.Acquire810
