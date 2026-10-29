module

public import FV.Backend.Proof.StockShiftBodyRefines
public import FV.Backend.Proof.StockMulNotrap

@[expose] public section

namespace Backend.Stock.Proof.ShiftBody
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

theorem shift_inst_notrap {inst : Clif.Inst} (family : Family inst)
    (fr : Clif.Frame) (cm : Clif.Mem) (c : Clif.TrapCode) : Clif.evalInst fr cm inst ≠ .trap c := by
  rcases family with old | ⟨kind,ty,x,y,rfl⟩
  · exact MulBody.mul_inst_notrap old fr cm c
  · cases getX : fr.getAs x ty with
    | trap code => exact False.elim (PureBody.frame_getAs_notrap fr x ty code getX)
    | stuck message => simp [Clif.evalInst,getX]
    | ok u =>
      cases count : fr.regs y with
      | none => cases kind <;> simp [Clif.evalInst,ScalarShift.Kind.cop,Clif.BinaryOp.isShift,getX,Clif.Frame.get,count]
      | some amount => cases kind <;> simp [Clif.evalInst,ScalarShift.Kind.cop,Clif.BinaryOp.isShift,getX,Clif.Frame.get,count,Clif.Sem.shift,Clif.Res.ofOption]

theorem shift_source_notrap {env : Clif.Env} {cp : Clif.Program} (fuel : Nat)
    (s : Clif.State) (callers : s.callers = []) (family : ∀ stm ∈ s.frame.body, Family stm.inst)
    {xs : List Nat} (ret : s.frame.term = .ret xs) (code : Clif.TrapCode) :
    Clif.runLoop env cp fuel s ≠ .trapped code := by
  apply PureBody.pure_source_notrap fuel s callers ?_ ret code
  intro stm member
  exact ⟨family_pure (family stm member),shift_inst_notrap (family stm member)⟩
end Backend.Stock.Proof.ShiftBody
