import FV.E2E.StockAcquirePairedIspecRefines
import FV.E2E.PairDriver
import FV.Backend.Proof.IselFamAluBBase

namespace E2E.StockAcquirePending
open Backend Backend.Proof
set_option autoImplicit false
set_option Elab.async false

/-- A complete pure model run derives paired execution under the unchanged Refines contract.
The disagreement set remains arbitrary and includes the original frame set. -/
theorem prun_ispec_paired {F Z : BitVec 64 → Prop} {isem : Sem}
    (refines : Refines F isem) (includes : ∀ addr,F addr → Z addr)
    {code : List MInst} {regs nextRegs : Nat → CV}
    (model : PRun F ispec code regs nextRegs) {before : W2}
    (related : SameWorld Z before.1 before.2) :
    ∃ after,seqRun (pairSem isem) code regs before = some (.fall nextRegs after) ∧
      SameWorld F after.1 before.1 ∧ SameWorld F after.2 before.2 ∧ SameWorld Z after.1 after.2 := by
  obtain ⟨leftModel,leftRun,leftFrame⟩ := model before.1
  obtain ⟨rightModel,rightRun,rightFrame⟩ := model before.2
  have lockstep : ∀ inst ∈ code,∀ uses left right outs nextLeft ctl otherOuts nextRight otherCtl,
      SameWorld Z left right → ispec inst uses left = some (outs,nextLeft,ctl) →
      ispec inst uses right = some (otherOuts,nextRight,otherCtl) →
      outs = otherOuts ∧ ctl = otherCtl ∧ SameWorld Z nextLeft nextRight := by
    intro inst member uses left right outs nextLeft ctl otherOuts nextRight otherCtl agreement first second
    obtain ⟨next,runNext,relatedNext⟩ := ispec_lockstep agreement first
    have equal := Option.some.inj (runNext.symm.trans second)
    simp only [Prod.mk.injEq] at equal
    obtain ⟨rfl,rfl,rfl⟩ := equal
    exact ⟨rfl,rfl,relatedNext⟩
  obtain ⟨rightModel',equal,paired,agreement⟩ := pair_fall (fun _ _ _ _ h => h) lockstep
    related leftRun rightRun
  have worldsEq := (SeqEnd.fall.inj equal).2
  rw [← worldsEq] at paired agreement
  obtain ⟨after,executed,leftActual,rightActual⟩ := paired_ispec_run_refines refines paired
  have leftKept := SameWorld.trans leftActual leftFrame
  have rightKept := SameWorld.trans rightActual rightFrame
  have finalAgreement := SameWorld.trans (SameWorld.mono includes leftActual)
    (SameWorld.trans agreement (SameWorld.symm (SameWorld.mono includes rightActual)))
  exact ⟨after,executed,leftKept,rightKept,finalAgreement⟩

end E2E.StockAcquirePending
