import FV.Backend.Proof.StockMemorySourceExecution
import FV.Clif.MemTrap

namespace Backend.Stock.Proof.OrdinaryBody
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private theorem getMany_notrap (fr : Clif.Frame) (xs : List Nat) (c : Clif.TrapCode) :
    fr.getMany xs ≠ .trap c := by
  induction xs generalizing c with
  | nil => simp [Clif.Frame.getMany]
  | cons x xs ih =>
    cases found : fr.get x with
    | trap code => exact False.elim (fr.get_ne_trap x code found)
    | stuck message => simp [Clif.Frame.getMany,found]
    | ok value =>
      cases rest : fr.getMany xs with
      | trap code => exact False.elim ((ih code) rest)
      | stuck message => simp [Clif.Frame.getMany,found,rest]
      | ok values => simp [Clif.Frame.getMany,found,rest]

/-- Shared source-run no-trap composition from ordinary instruction facts. -/
theorem ordinary_source_notrap {env : Clif.Env} {cp : Clif.Program} (fuel : Nat)
    (s : Clif.State) (callers : s.callers = [])
    (family : ∀ stm ∈ s.frame.body, OrdinaryInst stm.inst ∧ ∀ fr cm c, Clif.evalInst fr cm stm.inst ≠ .trap c)
    {xs : List Nat} (ret : s.frame.term = .ret xs) (code : Clif.TrapCode) :
    Clif.runLoop env cp fuel s ≠ .trapped code := by
  induction fuel generalizing s with
  | zero => simp
  | succ fuel ih =>
    rw [Clif.runLoop_succ]
    cases remaining : s.frame.body with
    | nil =>
      rw [Clif.step_term env cp s remaining,ret,Clif.stepTerm]
      cases values : s.frame.getMany xs with
      | trap c => exact False.elim (getMany_notrap s.frame xs c values)
      | stuck message => simp
      | ok vals =>
        simp only [Clif.StepResult.ofRes]
        by_cases typed : vals.map (·.ty) = Clif.AbiParam.tys s.frame.func.sig.returns <;>
          simp [Clif.returnValues,Clif.checkTys,Clif.Res.check,callers,Clif.StepResult.ofRes,typed]
    | cons stm rest =>
      have instFamily := family stm (by simp [remaining])
      rw [Clif.step_inst env cp s stm rest remaining
        instFamily.1.1 instFamily.1.2]
      cases evaluated : Clif.evalInst s.frame s.mem stm.inst with
      | trap c => exact False.elim (instFamily.2 s.frame s.mem c evaluated)
      | stuck message => simp
      | ok pair =>
        rcases pair with ⟨values,cm⟩
        simp only [Clif.StepResult.ofRes,Clif.continueWith]
        cases written : s.frame.regs.setMany stm.results values with
        | none => simp
        | some regs =>
          simp only
          apply ih {s with frame := {s.frame with regs,body := rest},mem := cm} callers ?_ ret
          intro other member
          apply family other
          rw [remaining]
          exact List.mem_cons_of_mem _ member

end Backend.Stock.Proof.OrdinaryBody
