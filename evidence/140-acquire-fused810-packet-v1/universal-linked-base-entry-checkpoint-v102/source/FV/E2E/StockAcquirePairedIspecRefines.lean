import FV.E2E.StockAcquireSeqRefinesSimulation

namespace E2E.StockAcquirePending
open Backend Backend.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Existing Refines transfers a paired ispec step without changing either output list.
Each actual world remains related to its own model world. -/
theorem paired_ispec_step_refines {F : BitVec 64 → Prop} {isem : Sem}
    (refines : Refines F isem) {inst : MInst} {uses outs : List CV} {ctl : Ctl}
    {before after actualBefore : W2}
    (left : SameWorld F actualBefore.1 before.1) (right : SameWorld F actualBefore.2 before.2)
    (step : pairSem ispec inst uses before = some (outs,after,ctl)) :
    ∃ actualAfter,pairSem isem inst uses actualBefore = some (outs,actualAfter,ctl) ∧
      SameWorld F actualAfter.1 after.1 ∧ SameWorld F actualAfter.2 after.2 := by
  obtain ⟨first,second⟩ := pairSem_inv step
  obtain ⟨modelLeft,onLeft,leftRel⟩ := ispec_lockstep (SameWorld.symm left) first
  obtain ⟨modelRight,onRight,rightRel⟩ := ispec_lockstep (SameWorld.symm right) second
  obtain ⟨nextLeft,runLeft,leftActual⟩ := refines _ _ _ _ _ onLeft
  obtain ⟨nextRight,runRight,rightActual⟩ := refines _ _ _ _ _ onRight
  exact ⟨(nextLeft,nextRight),pairSem_eq runLeft runRight,
    SameWorld.trans leftActual (SameWorld.symm leftRel),
    SameWorld.trans rightActual (SameWorld.symm rightRel)⟩

/-- Complete paired ispec execution transfers through the unchanged Refines contract. -/
theorem paired_ispec_run_refines {F : BitVec 64 → Prop} {isem : Sem}
    (refines : Refines F isem) {code : List MInst} {regs nextRegs : Nat → CV}
    {before after : W2} (run : seqRun (pairSem ispec) code regs before = some (.fall nextRegs after)) :
    ∃ actualAfter,seqRun (pairSem isem) code regs before = some (.fall nextRegs actualAfter) ∧
      SameWorld F actualAfter.1 after.1 ∧ SameWorld F actualAfter.2 after.2 := by
  apply seqRun_fall_simulation (R := fun actual model : W2 =>
    SameWorld F actual.1 model.1 ∧ SameWorld F actual.2 model.2) code ?_
    regs before nextRegs after run before ⟨SameWorld.refl _ _,SameWorld.refl _ _⟩
  intro inst member uses model actual outs next ctl related step
  exact paired_ispec_step_refines refines related.1 related.2 step

end E2E.StockAcquirePending
