import FV.Backend.Proof.StockArithmeticBodyRefines
namespace Backend.Stock.Proof.ArithmeticBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- The actual reference evaluator supplies the indexed arithmetic source step;
source/context/result correspondence is derived from successful Stock lowering. -/
theorem actual_arithmetic_source_step {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body) {record : ScanRecord} {j : Nat} {stm : Clif.Stmt}
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f event.block + j)
    (subtract : Bool) {ty : Clif.Ty} {x y : Nat}
    (shape : stm.inst = .binary (if subtract then .isub else .iadd) ty x y)
    {env : Clif.Env} {cp : Clif.Program} {s t : Clif.State} {rest : List Clif.Stmt}
    (remaining : s.frame.body = stm :: rest) (next : Clif.step env cp s = .next t) :
    IndexedSourceInst env cp f event.ctx event.block record.inst
      (j,s.frame,s.mem) (j+1,t.frame,t.mem) := by
  obtain ⟨info,source,clif,results⟩ := body_source_info run events split statement current
  have remaining' : s.frame.body = ⟨info.results,.binary (if subtract then .isub else .iadd) ty x y⟩ :: rest := by
    rw [remaining,results,← shape]
  unfold Clif.step at next
  rw [remaining'] at next
  cases evaluated : Clif.evalInst s.frame s.mem (.binary (if subtract then .isub else .iadd) ty x y) with
  | trap code => simp only [evaluated,Clif.StepResult.ofRes] at next; cases next
  | stuck message => simp only [evaluated,Clif.StepResult.ofRes] at next; cases next
  | ok value =>
    obtain ⟨vals,mem⟩ := value
    simp only [evaluated,Clif.StepResult.ofRes] at next
    unfold Clif.continueWith at next
    cases written : s.frame.regs.setMany info.results vals with
    | none => simp only [written] at next; cases next
    | some regs =>
      simp only [written] at next
      cases next
      refine ⟨current,rfl,info,_,vals,regs,rest,source,?_,remaining',?_,written,rfl⟩
      · rw [clif,shape]
      · exact evaluated

end Backend.Stock.Proof.ArithmeticBody
