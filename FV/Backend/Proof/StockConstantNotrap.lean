module

public import FV.Backend.Proof.StockConstantBodyRefines
public import FV.Backend.Proof.StockLogicalNotrap

@[expose] public section

namespace Backend.Stock.Proof.ConstantBody
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

/-- Constants and the retained logical/mixed family cannot trap. The shared
source-run proof keeps malformed operands' stuck behavior distinct from traps. -/
theorem constant_source_notrap {env : Clif.Env} {cp : Clif.Program} (fuel : Nat)
    (s : Clif.State) (callers : s.callers = [])
    (family : ∀ stm ∈ s.frame.body, Family stm.inst)
    {xs : List Nat} (ret : s.frame.term = .ret xs) (code : Clif.TrapCode) :
    Clif.runLoop env cp fuel s ≠ .trapped code := by
  apply PureBody.pure_source_notrap fuel s callers ?_ ret code
  intro stm member
  have instFamily := family stm member
  refine ⟨family_pure instFamily,?_⟩
  intro fr cm c
  rcases instFamily with old | ⟨ty,imm,shape⟩
  · exact LogicalBody.logical_inst_notrap fr cm old c
  · rw [shape]; simp [Clif.evalInst]

end Backend.Stock.Proof.ConstantBody
