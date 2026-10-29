module

public import FV.Backend.Proof.StockCastFamily
public import FV.Backend.Proof.StockShiftNotrap

@[expose] public section

namespace Backend.Stock.Proof.CastBody
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

theorem cast_inst_notrap {inst : Clif.Inst} (family : Family inst)
    (fr : Clif.Frame) (cm : Clif.Mem) (c : Clif.TrapCode) : Clif.evalInst fr cm inst ≠ .trap c := by
  rcases family with old | ⟨op,ty,x,rfl⟩ | ⟨ty,x,rfl⟩
  · exact ShiftBody.shift_inst_notrap old fr cm c
  · cases getX : fr.regs x with
    | none => simp [Clif.evalInst,Clif.Frame.get,getX]
    | some value =>
      by_cases width : value.ty.width < ty.width
      all_goals cases op <;> simp [Clif.evalInst,Clif.Frame.get,getX,Clif.Res.check,width]
  · cases getX : fr.regs x with
    | none => simp [Clif.evalInst,Clif.Frame.get,getX]
    | some value =>
      by_cases width : ty.width < value.ty.width
      all_goals simp [Clif.evalInst,Clif.Frame.get,getX,Clif.Res.check,width]

theorem cast_source_notrap {env : Clif.Env} {cp : Clif.Program} (fuel : Nat)
    (s : Clif.State) (callers : s.callers = []) (family : ∀ stm ∈ s.frame.body,Family stm.inst)
    {xs : List Nat} (ret : s.frame.term = .ret xs) (code : Clif.TrapCode) :
    Clif.runLoop env cp fuel s ≠ .trapped code := by
  apply PureBody.pure_source_notrap fuel s callers ?_ ret code
  intro stm member
  exact ⟨family_pure (family stm member),cast_inst_notrap (family stm member)⟩
end Backend.Stock.Proof.CastBody
