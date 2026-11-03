import FV.Backend.Proof.StockAcquireSelectedIntervalMemory

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The established bare source boundary interprets calls through its arbitrary environment. -/
theorem bare_source_statement_step (env : Clif.Env) (s : Clif.State) (stm : Clif.Stmt)
    (rest : List Clif.Stmt) (remaining : s.frame.body = stm::rest) :
    Clif.step env {funcs := []} s = Clif.StepResult.ofRes
      (instOutcome env {funcs := []} s.frame s.mem stm.inst)
      (fun (values,memory) => Clif.continueWith s rest stm.results values memory) := by
  apply step_stmt env {funcs := []} s stm rest remaining
  · intro fn args same e found
    rfl
  · intro sig callee args same cv found g member
    cases member

/-- A successful actual bare source step supplies the exact indexed instruction relation. -/
theorem bare_source_next_result {env : Clif.Env} {ctx : Ctx} {slot : Nat} {info : IInfo}
    {stm : Clif.Stmt} {s t : Clif.State} {rest : List Clif.Stmt}
    (installed : ctx.insts[slot]? = some info) (source : info.clif = some stm.inst)
    (results : info.results = stm.results) (remaining : s.frame.body = stm::rest)
    (next : Clif.step env {funcs := []} s = .next t) :
    SourceInstResult env {funcs := []} ctx slot (s.frame,s.mem) (t.frame,t.mem) ∧
      t.frame.body = rest := by
  rw [bare_source_statement_step env s stm rest remaining] at next
  cases evaluated : instOutcome env {funcs := []} s.frame s.mem stm.inst with
  | trap code => simp only [evaluated,Clif.StepResult.ofRes] at next; cases next
  | stuck message => simp only [evaluated,Clif.StepResult.ofRes] at next; cases next
  | ok value =>
    obtain ⟨values,memory⟩ := value
    simp only [evaluated,Clif.StepResult.ofRes] at next
    unfold Clif.continueWith at next
    cases written : s.frame.regs.setMany stm.results values with
    | none => simp only [written] at next; cases next
    | some regs =>
      simp only [written] at next
      cases next
      refine ⟨⟨info,stm.inst,values,regs,rest,installed,source,?_,evaluated,?_,rfl⟩,rfl⟩
      · rw [remaining,results]
      · rw [results]
        exact written

end Backend.Stock.Proof.Acquire810
