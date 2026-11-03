import FV.Backend.Proof.StockAcquireSourceProgramReach

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- The original program's MapFaults supplies the selected producer's exact mapped access. -/
theorem source_endpoint_atomic_fault_program {f : Clif.Function} {event : BlockScanEvent} {record : ScanRecord}
    (R : SourceEndpointReceipt f event record) {env : Clif.Env} {program : Clif.Program} {initial atFault : Clif.State}
    {code : Clif.TrapCode} {mp : ArmFault.MemMap}
    (faults : MapFaults mp env program initial) (reachable : Reach env program initial atFault)
    (failed : SourceInstFault env program event.ctx R.producer (atFault.frame,atFault.mem) code) :
    ∃ pointer,atFault.frame.get R.pointer = .ok pointer ∧ R.flags.trapCode = some code ∧
      ∃ j < R.ty.bytes,mp (BitVec.ofNat 64 (Clif.effAddr pointer 0)+BitVec.ofNat 64 j) = .none := by
  obtain ⟨info,inst,rest,installed,source,body,evaluated⟩ := failed
  have infoEq := Option.some.inj (installed.symm.trans R.installed)
  subst info
  have instEq := Option.some.inj (source.symm.trans R.source)
  subst inst
  change Clif.evalInst atFault.frame atFault.mem (.atomicLoad R.ty R.flags R.pointer) = .trap code at evaluated
  obtain ⟨pointer,found,aligned,invalid,flag⟩ := atomic_source_eval_trap evaluated
  have stepped : Clif.step env program atFault = .trapped code := by
    rw [step_stmt env program atFault ⟨R.info.results,.atomicLoad R.ty R.flags R.pointer⟩ rest body
      (by intro fn args same;cases same) (by intro sig callee args same;cases same)]
    change Clif.StepResult.ofRes (Clif.evalInst atFault.frame atFault.mem (.atomicLoad R.ty R.flags R.pointer)) _ = _
    rw [evaluated]
    rfl
  have access : Clif.MemTrapAt env program atFault code (Clif.effAddr pointer 0) R.ty.bytes :=
    ⟨stepped,invalid,⟨⟨R.info.results,.atomicLoad R.ty R.flags R.pointer⟩,rest,body,.atomicLoad found⟩⟩
  obtain ⟨j,bound,unmapped⟩ := faults atFault code _ _ reachable access
  refine ⟨pointer,found,flag,j,bound,?_⟩
  simpa only [BitVec.ofNat_add] using unmapped

/-- Actual source history derives the original program reachability needed by MapFaults. -/
theorem source_endpoint_atomic_fault_program_prefix {f : Clif.Function} {event : BlockScanEvent} {record : ScanRecord}
    (R : SourceEndpointReceipt f event record) {env : Clif.Env} {program : Clif.Program} {initial : Clif.State}
    {indices : List Nat} {atFault : Clif.Frame × Clif.Mem} {code : Clif.TrapCode} {mp : ArmFault.MemMap}
    (faults : MapFaults mp env program initial)
    (executed : SourceSteps (SourceInstResult env program event.ctx) indices (initial.frame,initial.mem) atFault)
    (failed : SourceInstFault env program event.ctx R.producer atFault code) :
    ∃ pointer,atFault.1.get R.pointer = .ok pointer ∧ R.flags.trapCode = some code ∧
      ∃ j < R.ty.bytes,mp (BitVec.ofNat 64 (Clif.effAddr pointer 0)+BitVec.ofNat 64 j) = .none := by
  have reached := source_steps_program_reach initial.callers executed
  have initialState : (⟨initial.frame,initial.callers,initial.mem⟩ : Clif.State) = initial := by cases initial;rfl
  rw [initialState] at reached
  exact source_endpoint_atomic_fault_program R faults reached failed

end Backend.Stock.Proof.Acquire810
