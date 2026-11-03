import FV.Backend.Proof.StockMemorySourceExecution
import FV.Backend.Proof.StockArithmeticBodyRefines
import FV.Backend.Proof.LowerSim

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- An actual ordinary source result is an actual CLIF step with unchanged callers. -/
theorem ordinary_source_result_step {env : Clif.Env} {cp : Clif.Program} {ctx : Ctx} {i : Nat}
    {s t : Clif.Frame × Clif.Mem} (result : SourceInstResult env cp ctx i s t)
    (family : ∀ info inst,ctx.insts[i]? = some info → info.clif = some inst →
      OrdinaryBody.OrdinaryInst inst)
    (callers : List (Clif.Frame × List Nat)) :
    Clif.step env cp ⟨s.1,callers,s.2⟩ = .next ⟨t.1,callers,t.2⟩ := by
  obtain ⟨info,inst,vals,regs,rest,found,original,remaining,evaluated,written,updated⟩ := result
  have ordinary := family info inst found original
  have outcome : instOutcome env cp s.1 s.2 inst = Clif.evalInst s.1 s.2 inst := by
    cases inst <;> try rfl
    all_goals first
      | exact False.elim (ordinary.1 _ _ rfl)
      | exact False.elim (ordinary.2 _ _ _ rfl)
  rw [outcome] at evaluated
  rw [Clif.step_inst env cp ⟨s.1,callers,s.2⟩ ⟨info.results,inst⟩ rest remaining ordinary.1 ordinary.2]
  simp only [evaluated,Clif.StepResult.ofRes,Clif.continueWith,written,updated]

/-- Indexed body execution retains the actual source reachability relation. -/
theorem ordinary_source_steps_reach {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    (family : ∀ stmt ∈ b.body,OrdinaryBody.OrdinaryInst stmt.inst)
    {env : Clif.Env} {cp : Clif.Program} {indices : List Nat} {s t : SourcePoint}
    (positions : ∀ i ∈ indices,∃ j stmt,b.body[j]? = some stmt ∧ i = blockStart f event.block+j)
    (steps : SourceSteps (IndexedSourceInst env cp f event.ctx event.block) indices s t)
    (callers : List (Clif.Frame × List Nat)) :
    Reach env cp ⟨s.2.1,callers,s.2.2⟩ ⟨t.2.1,callers,t.2.2⟩ := by
  induction steps with
  | nil s => exact .refl _
  | @cons i indices s middle t first tail ih =>
    obtain ⟨j,stmt,statement,current⟩ := positions i (List.mem_cons_self ..)
    obtain ⟨info,found,original,results⟩ := ArithmeticBody.body_source_info run events split
      (record := ⟨i,default,default⟩) statement current
    have localFamily : ∀ info' inst,event.ctx.insts[i]? = some info' → info'.clif = some inst →
        OrdinaryBody.OrdinaryInst inst := by
      intro info' inst found' original'
      cases Option.some.inj (found.symm.trans found')
      cases Option.some.inj (original.symm.trans original')
      exact family stmt (List.mem_of_getElem? statement)
    exact .step (ordinary_source_result_step first.2.2 localFamily callers)
      (ih (fun i member => positions i (List.mem_cons_of_mem _ member)))

end Backend.Stock.Proof
