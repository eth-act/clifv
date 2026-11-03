import FV.Backend.Proof.StockAcquireSourceFaultPrefix

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual trapped execution either faults inside the original slice or reaches its exact continuation. -/
theorem bare_trapped_source_slice {ctx : Ctx} {block : Clif.Block} {base : Nat}
    (slots : ∀ j stm,block.body[j]? = some stm →
      ∃ info,ctx.insts[base+j]? = some info ∧ info.clif = some stm.inst ∧ info.results = stm.results)
    (count : Nat) {env : Clif.Env} {start fuel : Nat} {s : Clif.State} {code : Clif.TrapCode}
    (inside : start+count ≤ block.body.length) (remaining : s.frame.body = block.body.drop start)
    (trapped : Clif.runLoop env {funcs := []} fuel s = .trapped code) :
    SourceTrapSteps (SourceInstResult env {funcs := []} ctx) (SourceInstFault env {funcs := []} ctx)
      (List.range' (base+start) count) (s.frame,s.mem) code ∨
    ∃ t left,left+count = fuel ∧ Clif.runLoop env {funcs := []} left t = .trapped code ∧
      t.frame.body = block.body.drop (start+count) ∧
      SourceSteps (SourceInstResult env {funcs := []} ctx) (List.range' (base+start) count)
        (s.frame,s.mem) (t.frame,t.mem) := by
  induction count generalizing start fuel s with
  | zero => exact Or.inr ⟨s,fuel,by omega,trapped,by simpa using remaining,.nil _⟩
  | succ count ih =>
    have headInside : start < block.body.length := by omega
    let stm := block.body[start]
    have statement : block.body[start]? = some stm := List.getElem?_eq_getElem headInside
    have head : s.frame.body = stm::block.body.drop (start+1) := by
      rw [remaining,List.drop_eq_getElem_cons headInside]
    obtain ⟨info,installed,source,results⟩ := slots start stm statement
    cases fuel with
    | zero => cases trapped
    | succ fuel =>
      rw [Clif.runLoop_succ,bare_source_statement_step env s stm _ head] at trapped
      cases evaluated : instOutcome env {funcs := []} s.frame s.mem stm.inst with
      | trap actualCode =>
        simp only [evaluated,Clif.StepResult.ofRes] at trapped
        cases trapped
        apply Or.inl
        rw [List.range'_succ]
        exact .here ⟨info,stm.inst,block.body.drop (start+1),installed,source,by rw [head,results],evaluated⟩
      | stuck message => simp only [evaluated,Clif.StepResult.ofRes] at trapped; cases trapped
      | ok value =>
        obtain ⟨vs,cm⟩ := value
        simp only [evaluated,Clif.StepResult.ofRes] at trapped
        unfold Clif.continueWith at trapped
        cases written : s.frame.regs.setMany stm.results vs with
        | none => simp only [written] at trapped; cases trapped
        | some regs =>
          simp only [written] at trapped
          let next : Clif.State := {s with frame := {s.frame with regs,body := block.body.drop (start+1)},mem := cm}
          have stepped : Clif.step env {funcs := []} s = .next next := by
            rw [bare_source_statement_step env s stm _ head,evaluated]
            simp only [Clif.StepResult.ofRes,Clif.continueWith,written]
            rfl
          obtain ⟨actual,body⟩ := bare_source_next_result installed source results head stepped
          rcases ih (start := start+1) (by omega) body trapped with early | ⟨t,left,total,ends,rest,tail⟩
          · apply Or.inl
            rw [List.range'_succ]
            simpa only [Nat.add_assoc] using SourceTrapSteps.next actual early
          · apply Or.inr
            refine ⟨t,left,by omega,ends,?_,?_⟩
            · simpa only [Nat.add_assoc,Nat.add_comm 1 count] using rest
            · rw [List.range'_succ]
              simpa only [Nat.add_assoc] using SourceSteps.cons actual tail

end Backend.Stock.Proof.Acquire810
