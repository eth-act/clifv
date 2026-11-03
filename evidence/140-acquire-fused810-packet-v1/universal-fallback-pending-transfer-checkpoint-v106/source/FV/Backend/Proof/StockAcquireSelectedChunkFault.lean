import FV.Backend.Proof.StockAcquireSelectedChunkValue
import FV.Backend.Proof.StockAcquireHalt
import FV.Backend.Proof.StockAcquireSourceFault

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- A genuine selected source fault supplies its original mapped access, without a heap guard. -/
theorem source_endpoint_atomic_fault {f : Clif.Function} {event : BlockScanEvent} {record : ScanRecord}
    (R : SourceEndpointReceipt f event record) {env : Clif.Env} {initial atFault : Clif.State}
    {code : Clif.TrapCode} {mp : ArmFault.MemMap}
    (faults : MapFaults mp env {funcs := []} initial)
    (reachable : Reach env {funcs := []} initial atFault)
    (failed : SourceInstFault env {funcs := []} event.ctx R.producer (atFault.frame,atFault.mem) code) :
    ∃ pointer,atFault.frame.get R.pointer = .ok pointer ∧ R.flags.trapCode = some code ∧
      ∃ j < R.ty.bytes,mp (BitVec.ofNat 64 (Clif.effAddr pointer 0)+BitVec.ofNat 64 j) = .none := by
  obtain ⟨info,inst,rest,installed,source,body,evaluated⟩ := failed
  have infoEq := Option.some.inj (installed.symm.trans R.installed)
  subst info
  have instEq := Option.some.inj (source.symm.trans R.source)
  subst inst
  change Clif.evalInst atFault.frame atFault.mem (.atomicLoad R.ty R.flags R.pointer) = .trap code at evaluated
  obtain ⟨pointer,found,aligned,invalid,flag⟩ := atomic_source_eval_trap evaluated
  have stepped : Clif.step env {funcs := []} atFault = .trapped code := by
    rw [bare_source_statement_step env atFault ⟨R.info.results,.atomicLoad R.ty R.flags R.pointer⟩ rest body]
    change Clif.StepResult.ofRes (Clif.evalInst atFault.frame atFault.mem (.atomicLoad R.ty R.flags R.pointer)) _ = _
    rw [evaluated]
    rfl
  have access : Clif.MemTrapAt env {funcs := []} atFault code (Clif.effAddr pointer 0) R.ty.bytes :=
    ⟨stepped,invalid,⟨⟨R.info.results,.atomicLoad R.ty R.flags R.pointer⟩,rest,body,.atomicLoad found⟩⟩
  obtain ⟨j,bound,unmapped⟩ := faults atFault code _ _ reachable access
  refine ⟨pointer,found,flag,j,bound,?_⟩
  simpa only [BitVec.ofNat_add] using unmapped

/-- Actual retained selection binds its source fault to the exact original acquire at chunk index zero. -/
theorem stock_lower_acquire_selected_chunk_fault {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (R : SourceEndpointReceipt f event record) (pointerReg dest : Nat),
      record.output.emitted = #[.loadAcquire (CTy.ofClif R.ty) (.vreg dest .int) (.vreg pointerReg .int) R.flags] ∧
      ∀ (env : Clif.Env) (initial atFault : Clif.State) (mp : ArmFault.MemMap) (code : Clif.TrapCode),
        MapFaults mp env {funcs := []} initial → Reach env {funcs := []} initial atFault →
        SourceInstFault env {funcs := []} event.ctx R.producer (atFault.frame,atFault.mem) code →
        FrameTyped event.ctx atFault.frame → ∀ (regs : Nat → CV) (world : Arm.ArmState),
        ValueHeld event.ctx atFault.frame regs R.pointer →
        ∃ address bytes,AcquireAt (record.output.emitted[0]!) [regs pointerReg] world code address bytes ∧
          ∃ j < bytes,mp (address+BitVec.ofNat 64 j) = .none := by
  obtain ⟨R,pointerReg,dest,resultId,key,register,results,resultReg,fresh,chunk,resultRegisters,finalAlias,finalNum⟩ :=
    stock_lower_acquire_selected_chunk run scope dominated events records recorded emitted selectedId
  refine ⟨R,pointerReg,dest,chunk,?_⟩
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
  have address : lo64 (regs pointerReg) = BitVec.ofNat 64 (Clif.effAddr pointer 0) :=
    (lo64_of_holds pointerHeld pointerType).trans (effAddr_zero pointer).symm
  refine ⟨lo64 (regs pointerReg),(CTy.ofClif R.ty).bytes,?_,j,?_,?_⟩
  · rw [chunk]
    exact AcquireAt.acquire (atomTy_ofClif R.integer) flag
  · have bytes : (CTy.ofClif R.ty).bytes = R.ty.bytes := by cases R.ty <;> rfl
    rw [bytes]
    exact bound
  · rw [address]
    exact unmapped

end Backend.Stock.Proof.Acquire810
