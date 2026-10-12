import FV.Backend.Proof.DeadCleanupSem
import FV.Backend.Proof.RefinesCSem
import FV.Backend.Proof.MemRefines

namespace Backend.DeadCleanup
open Backend.Proof

/-- Proof-only value semantics: pure producers use their unchanged-world
specification; effects keep the existing concrete semantics. The emitted code
and the legacy lowering driver are unchanged by this definition. -/
noncomputable def valueSem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) : Sem :=
  fun i us w => if pureForm i then mspec ctx.slotBase i us w else csem F ctx X i us w

theorem valueSem_pure {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {i : MInst} {us outs : List CV} {w w' : Arm.ArmState} {ctl : Ctl}
    (hp : pureForm i = true) (h : valueSem F ctx X i us w = some (outs, w', ctl)) :
    w' = w ∧ ctl = .next := by
  simp only [valueSem, hp, ↓reduceIte] at h
  exact mspec_pure hp h

/-- Every specified pure producer can be realized by the existing semantics,
with the same definition values and control and a related concrete world. -/
theorem pure_mspec_csem {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {i : MInst} {us outs : List CV} {w w' : Arm.ArmState} {ctl : Ctl}
    (hp : pureForm i = true) (h : mspec ctx.slotBase i us w = some (outs, w', ctl)) :
    ∃ wc, csem F ctx X i us w = some (outs, wc, ctl) ∧ SameWorld F wc w' := by
  unfold mspec at h
  split at h <;> try { simp_all [pureForm, pureAlu] }
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (memRefines_csem F ctx X (syms := fun _ => none) rfl
      (fun _ _ h => by cases h)).2.2.1 _ _ w
  · exact refines_csem F ctx X _ _ _ _ _ h

/-- The source-side instruction specification is preserved. -/
theorem refines_valueSem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    Refines F (valueSem F ctx X) := by
  intro i us w outs w' ctl h
  by_cases hp : pureForm i = true
  · exact ⟨w', by simp [valueSem, hp, mspec_of_ispec h], SameWorld.refl F w'⟩
  · simpa [valueSem, hp] using refines_csem F ctx X i us w outs w' h

/-! Non-vacuity: an actual redundant integer instruction has a defined value
step and a corresponding concrete step, with arbitrary world contents. -/
example (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (w : Arm.ArmState) :
    ∃ outs wc, valueSem F ctx X deadMvn [0#128] w = some (outs, w, .next) ∧
      csem F ctx X deadMvn [0#128] w = some (outs, wc, .next) ∧ SameWorld F wc w := by
  obtain ⟨outs, hs⟩ : ∃ outs, mspec ctx.slotBase deadMvn [0#128] w = some (outs, w, .next) :=
    ⟨[ofX (~~~(0#64))], rfl⟩
  obtain ⟨wc, hc, hw⟩ := pure_mspec_csem (by decide : pureForm deadMvn = true) hs
  exact ⟨outs, wc, by simpa [valueSem, deadMvn, pureForm, pureAlu] using hs, hc, hw⟩

end Backend.DeadCleanup
