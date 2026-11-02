import FV.Backend.Proof.DeadCleanupSem
import FV.Backend.Proof.RefinesCSem
import FV.Backend.Proof.MemRefines

namespace Backend.DeadCleanup
open Backend.Proof

/-- Proof-only value semantics: pure producers and compares (`specForm`) use their
specification; effects keep the existing concrete semantics. The emitted code
and the legacy lowering driver are unchanged by this definition. -/
noncomputable def valueSem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) : Sem :=
  fun i us w => if specForm i then mspec ctx.slotBase i us w else csem F ctx X i us w

theorem valueSem_pure {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {i : MInst} {us outs : List CV} {w w' : Arm.ArmState} {ctl : Ctl}
    (hp : pureForm i = true) (h : valueSem F ctx X i us w = some (outs, w', ctl)) :
    w' = w ∧ ctl = .next := by
  simp only [valueSem, specForm_of_pure hp, ↓reduceIte] at h
  exact mspec_pure hp h

/-- `csem` runs a `jump` alike from every world. -/
theorem csem_jumpPlain (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    JumpPlain (csem F ctx X) := by
  intro l us w outs w' ctl h
  simp only [csem, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨rfl, ⟨0, rfl⟩, fun _ => rfl⟩

/-- A semantics that is `csem` on `jump`s runs them alike from every world. -/
theorem jumpPlain_of_csem {sem : Sem} {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    (h : ∀ l, sem (.jump l) = csem F ctx X (.jump l)) : JumpPlain sem := by
  intro l us w outs w' ctl hs
  rw [h l] at hs
  obtain ⟨hw, hj, hall⟩ := csem_jumpPlain F ctx X l us w outs w' ctl hs
  exact ⟨hw, hj, fun w0 => by rw [h l]; exact hall w0⟩

/-- The value semantics lets the next compare overwrite a compare's flags. -/
theorem valueSem_cmpOverwrite (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    CmpOverwrite (valueSem F ctx X) :=
  cmpOverwrite_of_mspec (sb := ctx.slotBase)
    (fun i hs => by funext us w; simp only [valueSem, hs, ↓reduceIte])
    (jumpPlain_of_csem (F := F) (ctx := ctx) (X := X) fun l => by
      funext us w; simp [valueSem, specForm, pureForm, cmpForm])

/-- Every specified pure producer or compare can be realized by the existing semantics,
with the same definition values and control and a related concrete world. -/
theorem spec_mspec_csem {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {i : MInst} {us outs : List CV} {w w' : Arm.ArmState} {ctl : Ctl}
    (hp : specForm i = true) (h : mspec ctx.slotBase i us w = some (outs, w', ctl)) :
    ∃ wc, csem F ctx X i us w = some (outs, wc, ctl) ∧ SameWorld F wc w' := by
  unfold mspec at h
  split at h <;> try { simp_all [specForm, cmpForm, pureForm, pureAlu] }
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact (memRefines_csem F ctx X (syms := fun _ => none) rfl
      (fun _ _ h => by cases h)).2.2.1 _ _ w
  · exact refines_csem F ctx X _ _ _ _ _ h

/-- Every specified pure producer can be realized by the existing semantics,
with the same definition values and control and a related concrete world. -/
theorem pure_mspec_csem {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {i : MInst} {us outs : List CV} {w w' : Arm.ArmState} {ctl : Ctl}
    (hp : pureForm i = true) (h : mspec ctx.slotBase i us w = some (outs, w', ctl)) :
    ∃ wc, csem F ctx X i us w = some (outs, wc, ctl) ∧ SameWorld F wc w' :=
  spec_mspec_csem (specForm_of_pure hp) h

/-- The source-side instruction specification is preserved. -/
theorem refines_valueSem (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    Refines F (valueSem F ctx X) := by
  intro i us w outs w' ctl h
  by_cases hp : specForm i = true
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
  exact ⟨outs, wc, by simpa [valueSem, specForm, deadMvn, pureForm, pureAlu] using hs, hc, hw⟩

/-- Non-vacuity of the compare premise: a compare under the value semantics continues. -/
example (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (w : Arm.ArmState) :
    ∃ w', valueSem F ctx X (.aluRRR .subS .size64 .xzr (.vreg 0 .int) (.vreg 1 .int))
      [0#128, 0#128] w = some ([], w', .next) :=
  ⟨_, rfl⟩

end Backend.DeadCleanup
