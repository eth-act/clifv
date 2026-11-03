import FV.Backend.Proof.StockAcquireSourceEndpointValues

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Returned original execution supplies the successful extension value at the actual consumer. -/
theorem bare_returned_uextend {env : Clif.Env} {s : Clif.State} {stm : Clif.Stmt}
    {rest : List Clif.Stmt} {target : Clif.Ty} {value fuel : Nat}
    {values : List Clif.Val} {memory : Clif.Mem}
    (body : s.frame.body = stm::rest) (original : stm.inst = .extend .uextend target value)
    (returned : Clif.runLoop env {funcs := []} fuel s = .returned values memory) :
    ∃ widened nextMem,Clif.evalInst s.frame s.mem (.extend .uextend target value) = .ok ([widened],nextMem) := by
  cases fuel with
  | zero => cases returned
  | succ fuel =>
    rw [Clif.runLoop_succ,bare_source_statement_step env s stm rest body,original] at returned
    change (match Clif.StepResult.ofRes (Clif.evalInst s.frame s.mem (.extend .uextend target value))
      (fun (vs,cm) => Clif.continueWith s rest stm.results vs cm) with
      | .next next => Clif.runLoop env {funcs := []} fuel next
      | .done vs cm => .returned vs cm
      | .trapped code => .trapped code
      | .stuck message => .stuck message) = .returned values memory at returned
    cases evaluated : Clif.evalInst s.frame s.mem (.extend .uextend target value) with
    | trap code => simp only [evaluated,Clif.StepResult.ofRes] at returned;cases returned
    | stuck message => simp only [evaluated,Clif.StepResult.ofRes] at returned;cases returned
    | ok pair =>
      obtain ⟨vs,cm⟩ := pair
      obtain ⟨input,found,width,results,mem⟩ := evalInst_uextend_ok evaluated
      exact ⟨⟨target,Clif.Sem.uextend target.width input.bits⟩,cm,by rw [← results]⟩

end Backend.Stock.Proof.Acquire810
