module

public import FV.Clif.Run

@[expose] public section

namespace Backend.Stock.Proof.ArithmeticBody
set_option autoImplicit false
set_option Elab.async false

private theorem get_notrap (fr : Clif.Frame) (x : Nat) (c : Clif.TrapCode) :
    fr.get x ≠ .trap c := by
  cases found : fr.regs x <;> simp [Clif.Frame.get,Clif.Res.ofOption,found]

private theorem getAs_notrap (fr : Clif.Frame) (x : Nat) (ty : Clif.Ty) (c : Clif.TrapCode) :
    fr.getAs x ty ≠ .trap c := by
  cases found : fr.get x with
  | trap code => exact False.elim (get_notrap fr x code found)
  | stuck message => simp [Clif.Frame.getAs,found]
  | ok value => cases cast : value.as? ty <;> simp [Clif.Frame.getAs,found,Clif.Res.ofOption,cast]

private theorem getMany_notrap (fr : Clif.Frame) (xs : List Nat) (c : Clif.TrapCode) :
    fr.getMany xs ≠ .trap c := by
  induction xs generalizing c with
  | nil => simp [Clif.Frame.getMany]
  | cons x xs ih =>
    cases found : fr.get x with
    | trap code => exact False.elim (get_notrap fr x code found)
    | stuck message => simp [Clif.Frame.getMany,found]
    | ok value =>
      cases rest : fr.getMany xs with
      | trap code => exact False.elim ((ih code) rest)
      | stuck message => simp [Clif.Frame.getMany,found,rest]
      | ok values => simp [Clif.Frame.getMany,found,rest]

private theorem arithmetic_notrap (fr : Clif.Frame) (cm : Clif.Mem)
    (subtract : Bool) (ty : Clif.Ty) (x y : Nat) (c : Clif.TrapCode) :
    Clif.evalInst fr cm (.binary (if subtract then .isub else .iadd) ty x y) ≠ .trap c := by
  cases subtract <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,Clif.evalInst,Clif.BinaryOp.isShift]
  all_goals
    cases left : fr.getAs x ty with
    | trap code => exact False.elim (getAs_notrap fr x ty code left)
    | stuck message => simp
    | ok a =>
      cases right : fr.getAs y ty with
      | trap code => exact False.elim (getAs_notrap fr y ty code right)
      | stuck message => simp
      | ok b => simp

/-- Pure add/sub source bodies ending in return cannot produce a trap, even
when malformed operands instead make the executable semantics stuck. -/
theorem arithmetic_source_notrap {env : Clif.Env} {cp : Clif.Program} (fuel : Nat)
    (s : Clif.State) (callers : s.callers = [])
    (family : ∀ stm ∈ s.frame.body, ∃ subtract : Bool, ∃ ty x y,
      stm.inst = .binary (if subtract then .isub else .iadd) ty x y)
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
      obtain ⟨subtract,ty,x,y,shape⟩ := family stm (by simp [remaining])
      rw [Clif.step_inst env cp s stm rest remaining
        (by intro fn args h; rw [shape] at h; cases h)
        (by intro sig callee args h; rw [shape] at h; cases h)]
      cases evaluated : Clif.evalInst s.frame s.mem stm.inst with
      | trap c => exact False.elim (arithmetic_notrap s.frame s.mem subtract ty x y c (shape ▸ evaluated))
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

end Backend.Stock.Proof.ArithmeticBody
