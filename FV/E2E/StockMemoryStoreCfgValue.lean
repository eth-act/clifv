import FV.E2E.StockMemoryPairedFunction
import FV.Backend.Proof.DeadCleanupAdapter
import FV.Backend.StockMemoryStoreCfgCheck

namespace E2E.StockMemoryStoreCfg
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- The first memory adapter only needs effects whose value semantics is their
concrete semantics. This property is checked on the actual emitted artifact. -/
abbrev effectsOnly := Backend.Stock.MemoryStoreCfg.effectsOnly

theorem effectsOnly_instruction {vc : VCode} (checked : effectsOnly vc = true)
    {b k : Nat} {vb : VBlock} {i : MInst}
    (block : vc.blocks[b]? = some vb) (inst : vb.insts[k]? = some i) :
    pureForm i = false := by
  have blocks := List.all_eq_true.mp checked vb (by simpa using Array.mem_of_getElem? block)
  have instruction := List.all_eq_true.mp blocks i (by simpa using Array.mem_of_getElem? inst)
  cases i <;> simp_all [Backend.Stock.MemoryStoreCfg.effectInstruction,Backend.Stock.Memory.Store.effectInstruction,Backend.Stock.Memory.effectInstruction,pureForm]

/-- The checked effect whitelist also excludes the compare specifications added
by the current cleanup semantics. The preserved pure-only variant stays above. -/
private theorem effectsOnly_spec_instruction {vc : VCode} (checked : effectsOnly vc = true)
    {b k : Nat} {vb : VBlock} {i : MInst}
    (block : vc.blocks[b]? = some vb) (inst : vb.insts[k]? = some i) :
    specForm i = false := by
  have blocks := List.all_eq_true.mp checked vb (by simpa using Array.mem_of_getElem? block)
  have instruction := List.all_eq_true.mp blocks i (by simpa using Array.mem_of_getElem? inst)
  cases i <;> simp_all [Backend.Stock.MemoryStoreCfg.effectInstruction,Backend.Stock.Memory.Store.effectInstruction,Backend.Stock.Memory.effectInstruction,specForm,pureForm,cmpForm]

private theorem value_step {vc : VCode} (checked : effectsOnly vc = true)
    {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {s t : VConf CV Arm.ArmState}
    (step : VStep vc (csem F fc X) s t) : VStep vc (valueSem F fc X) s t := by
  cases step with
  | step block inst operands run arity next =>
    refine .step block inst operands ?_ arity next
    simpa only [valueSem,effectsOnly_spec_instruction checked block inst,Bool.false_eq_true,ite_false] using run

private theorem value_star {vc : VCode} (checked : effectsOnly vc = true)
    {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {s t : VConf CV Arm.ArmState}
    (path : Star (VStep vc (csem F fc X)) s t) : Star (VStep vc (valueSem F fc X)) s t := by
  induction path with
  | refl => exact .refl _
  | step first rest ih => exact .step (value_step checked first) ih

/-- On checked actual effect-only code, the production value consumer executes
exactly the concrete run, including its final world and ABI output tuple. -/
theorem return_value {vc : VCode} (checked : effectsOnly vc = true)
    {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {vs : VState CV Arm.ArmState}
    {us : List (Reg × Reg)} {outs : List CV} {world : Arm.ArmState}
    (returned : VRetFrom vc (csem F fc X) vs us outs world) :
    VRetFrom vc (valueSem F fc X) vs us outs world := by
  obtain ⟨b,k,ρ,w,vb,ops,results,path,block,inst,operands,values,run⟩ := returned
  have transferred := value_star checked path
  refine ⟨b,k,ρ,w,vb,ops,results,transferred,block,inst,operands,values,?_⟩
  simpa only [valueSem,effectsOnly_spec_instruction checked block inst,Bool.false_eq_true,ite_false] using run

end E2E.StockMemoryStoreCfg
