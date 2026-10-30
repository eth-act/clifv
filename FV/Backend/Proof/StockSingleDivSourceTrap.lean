import FV.Backend.Proof.StockPureNotrap
import FV.Backend.Proof.IselCmpDiv
import FV.Backend.Proof.LowerSim
namespace Backend.Stock.Proof.DivBody
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- With one local division and a return, a trapped original run must trap at
that division. A successful division followed by return cannot manufacture a trap. -/
theorem single_div_source_trap {env : Clif.Env} {cp : Clif.Program}
    {fuel : Nat} {s : Clif.State} {stm : Clif.Stmt}
    {op : Clif.DivOp} {ty : Clif.Ty} {x y : Nat} {xs : List Nat} {code : Clif.TrapCode}
    (remaining : s.frame.body = [stm]) (division : stm.inst = .div op ty x y)
    (callers : s.callers = []) (ret : s.frame.term = .ret xs)
    (trapped : Clif.runLoop env cp fuel s = .trapped code) :
    instOutcome env cp s.frame s.mem (.div op ty x y) = .trap code := by
  cases fuel with
  | zero => cases trapped
  | succ fuel =>
    have localStep : Clif.step env cp s =
        Clif.StepResult.ofRes (Clif.evalInst s.frame s.mem (.div op ty x y))
          (fun (vs,cm) => Clif.continueWith s [] stm.results vs cm) := by
      unfold Clif.step
      simp only [remaining,division]
    rw [Clif.runLoop_succ,localStep] at trapped
    cases eval : Clif.evalInst s.frame s.mem (.div op ty x y) with
    | trap c =>
      simp only [eval,Clif.StepResult.ofRes,Clif.Outcome.trapped.injEq] at trapped
      subst c
      exact eval
    | stuck message => simp only [eval,Clif.StepResult.ofRes] at trapped; cases trapped
    | ok value =>
      obtain ⟨vals,cm⟩ := value
      simp only [eval,Clif.StepResult.ofRes] at trapped
      unfold Clif.continueWith at trapped
      cases set : s.frame.regs.setMany stm.results vals with
      | none => simp only [set] at trapped; cases trapped
      | some regs =>
        simp only [set] at trapped
        exact False.elim (PureBody.pure_source_notrap fuel
          {s with frame := {s.frame with regs,body := []},mem := cm}
          callers (by simp) ret code trapped)

/-- A genuine local halting trace placed in the actual block supplies the
unchanged whole-VCode trap contract. -/
theorem trapRun_at {vc : VCode} {isem : Backend.Proof.Sem} {b k : Nat} {vb : VBlock}
    {ms : List MInst} {ρ : Nat → CV} {w : Arm.ArmState} {code : Clif.TrapCode}
    (placed : vc.blocks[b]? = some vb) (segment : SegAt vb k ms)
    (trap : TrapRun isem ms ρ w code) : VTrapFrom vc isem ⟨b,k,ρ,w⟩ code := by
  obtain ⟨offset,i,ops,ρ',w',outs,final,execution,trapCode⟩ := trap
  obtain ⟨path,bound,inst,operands,semantics,arity,control⟩ :=
    seqRun_stop_star placed segment execution
  exact ⟨b,k+offset,ρ',w',vb,i,ops,outs,final,path,placed,inst,operands,semantics,trapCode⟩

end Backend.Stock.Proof.DivBody
