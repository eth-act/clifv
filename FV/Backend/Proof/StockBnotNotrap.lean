import FV.Backend.Proof.StockBnotBodyRefines
import FV.Backend.Proof.StockConstantNotrap
import FV.Backend.Proof.StockLogicalNotrap

namespace Backend.Stock.Proof.BnotBody
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

/-- Reusable no-trap fact for each shipped source instruction. -/
theorem bnot_inst_notrap {inst : Clif.Inst} (family : Family inst)
    (fr : Clif.Frame) (cm : Clif.Mem) (c : Clif.TrapCode) : Clif.evalInst fr cm inst ≠ .trap c := by
  rcases family with old | ⟨ty,x,shape⟩
  · rcases old with logical | ⟨ty,imm,shape⟩
    · exact LogicalBody.logical_inst_notrap fr cm logical c
    · rw [shape]; simp [Clif.evalInst]
  · rw [shape]
    cases get : fr.getAs x ty with
    | ok u => simp [Clif.evalInst,get]
    | stuck message => simp [Clif.evalInst,get]
    | trap code =>
      have impossible : fr.getAs x ty ≠ .trap code := by
        cases reg : fr.regs x with
        | none => simp [Clif.Frame.getAs,Clif.Frame.get,Clif.Res.ofOption,reg]
        | some value =>
          cases cast : value.as? ty <;> simp [Clif.Frame.getAs,Clif.Frame.get,Clif.Res.ofOption,reg,cast]
      exact False.elim (impossible get)


/-- NOT and the retained constant/logical/mixed family cannot trap. The shared
source-run proof keeps malformed operands' stuck behavior distinct from traps. -/
theorem bnot_source_notrap {env : Clif.Env} {cp : Clif.Program} (fuel : Nat)
    (s : Clif.State) (callers : s.callers = [])
    (family : ∀ stm ∈ s.frame.body, Family stm.inst)
    {xs : List Nat} (ret : s.frame.term = .ret xs) (code : Clif.TrapCode) :
    Clif.runLoop env cp fuel s ≠ .trapped code := by
  apply PureBody.pure_source_notrap fuel s callers ?_ ret code
  intro stm member
  have instFamily := family stm member
  refine ⟨family_pure instFamily,?_⟩
  intro fr cm c
  exact bnot_inst_notrap instFamily fr cm c

end Backend.Stock.Proof.BnotBody
