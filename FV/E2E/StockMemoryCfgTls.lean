import FV.E2E.StockMemoryCfgValue

namespace E2E.StockMemoryCfg
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- TLS flags are irrelevant to the checked CFG effects. -/
def fixedTlsFlags (X : ExtSem) : ExtSem := {X with tlsFlags := fun _ _ => Arm.PState.zero}

theorem fixedTlsFlags_ok (F : BitVec 64 → Prop) (X : ExtSem) : XTls F (fixedTlsFlags X) := by
  intro Z n w w' subset same
  rfl

private theorem instruction_tls {vc : VCode} (checked : effectsOnly vc = true)
    {b k : Nat} {vb : VBlock} {i : MInst}
    (block : vc.blocks[b]? = some vb) (inst : vb.insts[k]? = some i)
    (F : BitVec 64 → Prop) (fc : FnCtx) (X : ExtSem) :
    csem F fc (fixedTlsFlags X) i = csem F fc X i := by
  have blocks := List.all_eq_true.mp checked vb (by simpa using Array.mem_of_getElem? block)
  have good := List.all_eq_true.mp blocks i (by simpa using Array.mem_of_getElem? inst)
  cases i <;> simp only [Backend.Stock.MemoryCfg.effectInstruction] at good <;> try cases good
  all_goals rfl

private theorem step_tls {vc : VCode} (checked : effectsOnly vc = true)
    {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {s t : VConf CV Arm.ArmState}
    (step : VStep vc (csem F fc (fixedTlsFlags X)) s t) : VStep vc (csem F fc X) s t := by
  cases step with
  | step block inst operands run arity next =>
    refine .step block inst operands ?_ arity next
    rwa [instruction_tls checked block inst F fc X] at run

private theorem star_tls {vc : VCode} (checked : effectsOnly vc = true)
    {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {s t : VConf CV Arm.ArmState}
    (steps : Star (VStep vc (csem F fc (fixedTlsFlags X))) s t) :
    Star (VStep vc (csem F fc X)) s t := by
  induction steps with
  | refl => exact .refl _
  | step first rest ih => exact .step (step_tls checked first) ih

/-- The actual code returns identically with the original TLS flags, for any external semantics. -/
theorem return_original_tls {vc : VCode} (checked : effectsOnly vc = true)
    {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {vs : VState CV Arm.ArmState}
    {us : List (Reg × Reg)} {outs : List CV} {world : Arm.ArmState}
    (returned : VRetFrom vc (csem F fc (fixedTlsFlags X)) vs us outs world) :
    VRetFrom vc (csem F fc X) vs us outs world := by
  obtain ⟨b,k,ρ,w,vb,ops,results,path,block,inst,operands,values,run⟩ := returned
  refine ⟨b,k,ρ,w,vb,ops,results,star_tls checked path,block,inst,operands,values,?_⟩
  rwa [instruction_tls checked block inst F fc X] at run

end E2E.StockMemoryCfg
