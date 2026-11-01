import FV.Backend.Proof.StockMemorySourceExecution
import FV.Backend.Proof.StockLocalSourceTrap

namespace Backend.Stock.Proof.OrdinaryBody
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private theorem trap_step {env : Clif.Env} {cp : Clif.Program}
    {s : Clif.State} {stm : Clif.Stmt} {rest : List Clif.Stmt}
    (remaining : s.frame.body = stm :: rest) (family : OrdinaryInst stm.inst) :
    Clif.step env cp s = Clif.StepResult.ofRes (Clif.evalInst s.frame s.mem stm.inst)
      (fun (vs,cm) => Clif.continueWith s rest stm.results vs cm) := by
  exact Clif.step_inst env cp s stm rest remaining family.1 family.2

private theorem trap_outcome {env : Clif.Env} {cp : Clif.Program}
    {fr : Clif.Frame} {cm : Clif.Mem} {inst : Clif.Inst} (family : OrdinaryInst inst) :
    instOutcome env cp fr cm inst = Clif.evalInst fr cm inst := by
  cases inst <;> try rfl
  all_goals first
    | exact False.elim (family.1 _ _ rfl)
    | exact False.elim (family.2 _ _ _ rfl)

/-- Actual call-free execution supplies the original indexed trap, including memory effects. -/
theorem actual_ordinary_source_trap {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body) {j : Nat} {stm : Clif.Stmt}
    (statement : b.body[j]? = some stm) (family : OrdinaryInst stm.inst)
    {env : Clif.Env} {cp : Clif.Program} {s : Clif.State} {rest : List Clif.Stmt}
    (remaining : s.frame.body = stm :: rest) {code : Clif.TrapCode}
    (trapped : Clif.step env cp s = .trapped code) :
    LocalBody.IndexedSourceTrap env cp f event.ctx event.block (blockStart f event.block+j)
      (j,s.frame,s.mem) code := by
  obtain ⟨info,source,clif,results⟩ := ArithmeticBody.body_source_info run events split
    (record := ⟨blockStart f event.block+j,default,default⟩) statement rfl
  refine ⟨rfl,info,stm.inst,rest,source,clif,?_,?_⟩
  · rw [remaining,results]
  · rw [trap_outcome family]
    rw [trap_step remaining family] at trapped
    cases evaluated : Clif.evalInst s.frame s.mem stm.inst with
    | trap c =>
      simp only [evaluated,Clif.StepResult.ofRes,Clif.StepResult.trapped.injEq] at trapped
      cases trapped
      rfl
    | stuck message => simp only [evaluated,Clif.StepResult.ofRes] at trapped; cases trapped
    | ok pair =>
      obtain ⟨vs,cm⟩ := pair
      simp only [evaluated,Clif.StepResult.ofRes,Clif.continueWith] at trapped
      cases written : s.frame.regs.setMany stm.results vs <;> simp only [written] at trapped <;> cases trapped



end Backend.Stock.Proof.OrdinaryBody
