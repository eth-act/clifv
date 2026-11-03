import FV.Backend.Proof.StockAcquireBareSourceStep

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private theorem returned_next {env : Clif.Env} {ctx : Ctx} {slot : Nat} {info : IInfo}
    {stm : Clif.Stmt} {s : Clif.State} {rest : List Clif.Stmt} {fuel : Nat}
    {values : List Clif.Val} {memory : Clif.Mem}
    (installed : ctx.insts[slot]? = some info) (source : info.clif = some stm.inst)
    (results : info.results = stm.results) (remaining : s.frame.body = stm::rest)
    (returned : Clif.runLoop env {funcs := []} (fuel+1) s = .returned values memory) :
    ∃ t,Clif.step env {funcs := []} s = .next t ∧ t.frame.body = rest ∧
      Clif.runLoop env {funcs := []} fuel t = .returned values memory ∧
      SourceInstResult env {funcs := []} ctx slot (s.frame,s.mem) (t.frame,t.mem) := by
  rw [Clif.runLoop_succ,bare_source_statement_step env s stm rest remaining] at returned
  cases evaluated : instOutcome env {funcs := []} s.frame s.mem stm.inst with
  | trap code => simp only [evaluated,Clif.StepResult.ofRes] at returned; cases returned
  | stuck message => simp only [evaluated,Clif.StepResult.ofRes] at returned; cases returned
  | ok value =>
    obtain ⟨vs,cm⟩ := value
    simp only [evaluated,Clif.StepResult.ofRes] at returned
    unfold Clif.continueWith at returned
    cases written : s.frame.regs.setMany stm.results vs with
    | none => simp only [written] at returned; cases returned
    | some regs =>
      simp only [written] at returned
      let t : Clif.State := {s with frame := {s.frame with regs,body := rest},mem := cm}
      have stepped : Clif.step env {funcs := []} s = .next t := by
        rw [bare_source_statement_step env s stm rest remaining,evaluated]
        simp only [Clif.StepResult.ofRes,Clif.continueWith,written]
      obtain ⟨actual,body⟩ := bare_source_next_result installed source results remaining stepped
      exact ⟨t,stepped,body,returned,actual⟩

/-- The actual bare execution supplies every successful original body slice and its residual fuel. -/
theorem bare_returned_source_slice {ctx : Ctx} {block : Clif.Block} {base : Nat}
    (slots : ∀ j stm,block.body[j]? = some stm →
      ∃ info,ctx.insts[base+j]? = some info ∧ info.clif = some stm.inst ∧ info.results = stm.results)
    (count : Nat) {env : Clif.Env} {start fuel : Nat} {s : Clif.State}
    {values : List Clif.Val} {memory : Clif.Mem}
    (inside : start+count ≤ block.body.length) (remaining : s.frame.body = block.body.drop start)
    (returned : Clif.runLoop env {funcs := []} fuel s = .returned values memory) :
    ∃ t left,left+count = fuel ∧ Clif.runLoop env {funcs := []} left t = .returned values memory ∧
      t.frame.body = block.body.drop (start+count) ∧
      SourceSteps (SourceInstResult env {funcs := []} ctx) (List.range' (base+start) count)
        (s.frame,s.mem) (t.frame,t.mem) := by
  induction count generalizing start fuel s with
  | zero => exact ⟨s,fuel,by omega,returned,by simpa using remaining,.nil _⟩
  | succ count ih =>
    have headInside : start < block.body.length := by omega
    let stm := block.body[start]
    have statement : block.body[start]? = some stm := List.getElem?_eq_getElem headInside
    have head : s.frame.body = stm::block.body.drop (start+1) := by
      rw [remaining,List.drop_eq_getElem_cons headInside]
    obtain ⟨info,installed,source,results⟩ := slots start stm statement
    cases fuel with
    | zero => cases returned
    | succ fuel =>
      obtain ⟨next,stepped,body,continued,actual⟩ := returned_next installed source results head returned
      obtain ⟨t,left,total,ends,rest,tail⟩ := ih (start := start+1) (by omega) body continued
      refine ⟨t,left,by omega,ends,?_,?_⟩
      · simpa only [Nat.add_assoc,Nat.add_comm 1 count] using rest
      · rw [List.range'_succ]
        simpa only [Nat.add_assoc] using SourceSteps.cons actual tail

end Backend.Stock.Proof.Acquire810
