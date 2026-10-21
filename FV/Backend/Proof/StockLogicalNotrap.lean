import FV.Backend.Proof.StockLogicalSourceExecution
import FV.Backend.Proof.StockPureNotrap

/-! Actual source outcomes for the complete ordinary logical/mixed class. -/
namespace Backend.Stock.Proof.LogicalBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
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

private theorem family_notrap (fr : Clif.Frame) (cm : Clif.Mem)
    {inst : Clif.Inst} (family : Family inst) (c : Clif.TrapCode) :
    Clif.evalInst fr cm inst ≠ .trap c := by
  rcases family with ⟨subtract,ty,x,y,rfl⟩ | ⟨ty,condition,x,y,rfl⟩ | ⟨kind,ty,x,y,rfl⟩
  · exact arithmetic_notrap fr cm subtract ty x y c
  · simp only [Clif.evalInst]
    cases cond : fr.get condition with
    | trap code => exact False.elim (get_notrap fr condition code cond)
    | stuck message => simp
    | ok cv =>
      cases left : fr.getAs x ty with
      | trap code => exact False.elim (getAs_notrap fr x ty code left)
      | stuck message => simp
      | ok a =>
        cases right : fr.getAs y ty with
        | trap code => exact False.elim (getAs_notrap fr y ty code right)
        | stuck message => simp
        | ok b => simp

  · cases kind <;> simp only [LogicalSelected.Kind.cop,Clif.evalInst,Clif.BinaryOp.isShift]
    all_goals
      cases left : fr.getAs x ty with
      | trap code => exact False.elim (getAs_notrap fr x ty code left)
      | stuck message => simp
      | ok a =>
        cases right : fr.getAs y ty with
        | trap code => exact False.elim (getAs_notrap fr y ty code right)
        | stuck message => simp
        | ok b => simp

/-- Reusable local no-trap fact for the preserved logical/mixed syntax. -/
theorem logical_inst_notrap (fr : Clif.Frame) (cm : Clif.Mem)
    {inst : Clif.Inst} (family : Family inst) (code : Clif.TrapCode) :
    Clif.evalInst fr cm inst ≠ .trap code := family_notrap fr cm family code

/-- Pure select/add/sub/logical source bodies ending in return cannot produce a trap, even
when malformed operands instead make the executable semantics stuck. -/
theorem logical_source_notrap {env : Clif.Env} {cp : Clif.Program} (fuel : Nat)
    (s : Clif.State) (callers : s.callers = [])
    (family : ∀ stm ∈ s.frame.body, Family stm.inst)
    {xs : List Nat} (ret : s.frame.term = .ret xs) (code : Clif.TrapCode) :
    Clif.runLoop env cp fuel s ≠ .trapped code := by
  apply PureBody.pure_source_notrap fuel s callers ?_ ret code
  intro stm member
  have instFamily := family stm member
  refine ⟨?_,fun fr cm c => family_notrap fr cm instFamily c⟩
  rcases instFamily with ⟨subtract,ty,x,y,shape⟩ | ⟨ty,c,x,y,shape⟩ | ⟨kind,ty,x,y,shape⟩
  all_goals rw [shape]; rfl

end Backend.Stock.Proof.LogicalBody
