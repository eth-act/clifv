import FV.Backend.Proof.StockAcquireDeferredProducerRelation

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Indexed successful bare source outcomes reconstruct their actual step, with the original caller stack. -/
theorem source_inst_result_bare_step {env : Clif.Env} {ctx : Ctx} {slot : Nat}
    {before after : Clif.Frame × Clif.Mem} (callers : List (Clif.Frame × List Clif.ValueId))
    (executed : SourceInstResult env {funcs := []} ctx slot before after) :
    Clif.step env {funcs := []} ⟨before.1,callers,before.2⟩ = .next ⟨after.1,callers,after.2⟩ := by
  obtain ⟨info,inst,values,regs,rest,installed,source,body,evaluated,written,frame⟩ := executed
  rw [bare_source_statement_step env _ ⟨info.results,inst⟩ rest body,evaluated]
  simp only [Clif.StepResult.ofRes,Clif.continueWith,written]
  rw [frame]

/-- Actual indexed prefixes derive reachability; callers need no additional reachability certificate. -/
theorem source_steps_bare_reach {env : Clif.Env} {ctx : Ctx}
    {indices : List Nat} {before after : Clif.Frame × Clif.Mem} (callers : List (Clif.Frame × List Clif.ValueId))
    (executed : SourceSteps (SourceInstResult env {funcs := []} ctx) indices before after) :
    Reach env {funcs := []} ⟨before.1,callers,before.2⟩ ⟨after.1,callers,after.2⟩ := by
  induction executed with
  | nil => exact .refl _
  | cons head tail ih => exact .step (source_inst_result_bare_step callers head) ih

/-- The original MapFaults premise supplies the actual producer access from its executed prefix. -/
theorem source_endpoint_atomic_fault_from_prefix {f : Clif.Function} {event : BlockScanEvent} {record : ScanRecord}
    (R : SourceEndpointReceipt f event record) {env : Clif.Env} {initial : Clif.State}
    {indices : List Nat} {atFault : Clif.Frame × Clif.Mem} {code : Clif.TrapCode} {mp : ArmFault.MemMap}
    (faults : E2E.MapFaults mp env {funcs := []} initial)
    (executed : SourceSteps (SourceInstResult env {funcs := []} event.ctx) indices (initial.frame,initial.mem) atFault)
    (failed : SourceInstFault env {funcs := []} event.ctx R.producer atFault code) :
    ∃ pointer,atFault.1.get R.pointer = .ok pointer ∧ R.flags.trapCode = some code ∧
      ∃ j < R.ty.bytes,mp (BitVec.ofNat 64 (Clif.effAddr pointer 0)+BitVec.ofNat 64 j) = .none := by
  have reached := source_steps_bare_reach initial.callers executed
  have initialState : (⟨initial.frame,initial.callers,initial.mem⟩ : Clif.State) = initial := by cases initial;rfl
  rw [initialState] at reached
  exact source_endpoint_atomic_fault R faults reached failed

end Backend.Stock.Proof.Acquire810
