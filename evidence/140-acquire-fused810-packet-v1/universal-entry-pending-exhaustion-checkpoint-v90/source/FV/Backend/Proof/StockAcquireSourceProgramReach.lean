import FV.Backend.Proof.StockAcquireProgramStepConditions

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Successful indexed outcomes derive the actual step in any program, including external calls.
Internal program calls are not successful instOutcome cases; linked induction handles those activations. -/
theorem source_inst_result_program_step {env : Clif.Env} {program : Clif.Program} {ctx : Ctx} {slot : Nat}
    {before after : Clif.Frame × Clif.Mem} (callers : List (Clif.Frame × List Clif.ValueId))
    (executed : SourceInstResult env program ctx slot before after) :
    Clif.step env program ⟨before.1,callers,before.2⟩ = .next ⟨after.1,callers,after.2⟩ := by
  obtain ⟨info,inst,values,regs,rest,installed,source,body,evaluated,written,frame⟩ := executed
  have statement := step_stmt env program ⟨before.1,callers,before.2⟩ ⟨info.results,inst⟩ rest body
    (by
      intro fn args same ext declared
      simp only at same
      rw [same] at evaluated
      exact instOutcome_ok_direct_external declared evaluated)
    (by
      intro sig callee args same cv located g member
      simp only at same
      rw [same] at evaluated
      exact instOutcome_ok_indirect_external located evaluated g member)
  rw [statement,evaluated]
  simp only [Clif.StepResult.ofRes,Clif.continueWith,written]
  rw [frame]

/-- The actual successful indexed source prefix derives reachability in its original program. -/
theorem source_steps_program_reach {env : Clif.Env} {program : Clif.Program} {ctx : Ctx}
    {indices : List Nat} {before after : Clif.Frame × Clif.Mem} (callers : List (Clif.Frame × List Clif.ValueId))
    (executed : SourceSteps (SourceInstResult env program ctx) indices before after) :
    Reach env program ⟨before.1,callers,before.2⟩ ⟨after.1,callers,after.2⟩ := by
  induction executed with
  | nil => exact .refl _
  | cons head tail ih => exact .step (source_inst_result_program_step callers head) ih

end Backend.Stock.Proof.Acquire810
