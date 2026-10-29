module

public import FV.Backend.Proof.StockMulBodyRefines
public import FV.Backend.Proof.StockBnotNotrap

@[expose] public section

namespace Backend.Stock.Proof.MulBody
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

theorem mul_inst_notrap {inst : Clif.Inst} (family : Family inst)
    (fr : Clif.Frame) (cm : Clif.Mem) (c : Clif.TrapCode) : Clif.evalInst fr cm inst ≠ .trap c := by
  rcases family with old | ⟨ty,x,y,rfl⟩
  · exact BnotBody.bnot_inst_notrap old fr cm c
  · cases getX : fr.getAs x ty with
    | trap code => exact False.elim (PureBody.frame_getAs_notrap fr x ty code getX)
    | stuck message => simp [Clif.evalInst,getX]
    | ok u =>
      cases getY : fr.getAs y ty with
      | trap code => exact False.elim (PureBody.frame_getAs_notrap fr y ty code getY)
      | stuck message => simp [Clif.evalInst,getX,getY,Clif.BinaryOp.isShift]
      | ok v => simp [Clif.evalInst,getX,getY,Clif.BinaryOp.isShift]

theorem mul_source_notrap {env : Clif.Env} {cp : Clif.Program} (fuel : Nat)
    (s : Clif.State) (callers : s.callers = []) (family : ∀ stm ∈ s.frame.body, Family stm.inst)
    {xs : List Nat} (ret : s.frame.term = .ret xs) (code : Clif.TrapCode) :
    Clif.runLoop env cp fuel s ≠ .trapped code := by
  apply PureBody.pure_source_notrap fuel s callers ?_ ret code
  intro stm member
  exact ⟨family_pure (family stm member),mul_inst_notrap (family stm member)⟩
end Backend.Stock.Proof.MulBody
