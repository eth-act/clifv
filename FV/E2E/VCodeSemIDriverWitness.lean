import FV.Backend.Proof.VCodeSemIDriver
import FV.E2E.RegLevelDriverSem

/-!
# Witnesses for the driver facts under the counted semantics (`FV/Backend/Proof/VCodeSemIDriver.lean`)

* `driverSemG_csemI`: `DriverSemG.csemI` applied to `driverSem_csem` at every index: the driver
  facts hold for `csemI` with any call-indexed externals.
* `jump_csem`/`jump_csemI`: the lowering `[jump l]` of a CLIF `jump` is correct for `csem`, and
  by `LowerTermOk.csemI` for `csemI` (any counter invariant).
-/

namespace Backend.Proof.VCodeSemIDriverWitness

open Backend Backend.Proof Backend.Proof.Driver

/-- **The driver facts for `csemI`.** -/
theorem driverSemG_csemI (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSemI) :
    DriverSemG (csemI F ctx X) :=
  DriverSemG.csemI fun n => (driverSem_csem F ctx (X.at n)).toDriverSemG

/-- `[jump l]` is a correct `csem` lowering of a CLIF `jump` with target list `[l]`. -/
theorem jump_csem (F : BitVec 64 → Prop) (fctx : FnCtx) (X : ExtSem) (MR : MemRelT) (ctx : Ctx)
    (bc : Clif.BlockCall) (l : Label) (st : LState) :
    LowerTermOk (csem F fctx X) MR ctx (.jump bc) [l] st st [.jump l] where
  mono := Nat.le_refl _
  defs := fun m hm d hd => by
    simp only [List.mem_singleton] at hm
    subst hm
    have e : vdefs (MInst.jump l) = [] := rfl
    rw [e] at hd; cases hd
  run := fun fr cm ρ w _ _ _ hmr => by
    refine ⟨fun i hi => by simp at hi; subst hi; rfl, fun j hj => ?_⟩
    simp only [branchIdx] at hj
    cases hj
    have e : vuseNums (MInst.jump l) = [] := rfl
    have hu : UsesOk st fr [MInst.jump l] := by
      intro m hm u hu
      simp only [List.mem_singleton] at hm
      subst hm
      rw [e] at hu; cases hu
    exact ⟨hu, 0, .jump l, #[], ρ, w, [], w, rfl, rfl, hmr⟩

/-- **`LowerTermOk.csemI` on it**: the `jump` lowering is correct for the counted semantics. -/
theorem jump_csemI (F : BitVec 64 → Prop) (fctx : FnCtx) (X : ExtSemI) (MR : MemRelT)
    (Q : Clif.Mem → Nat → Prop) (ctx : Ctx) (bc : Clif.BlockCall) (l : Label) (st : LState) :
    LowerTermOk (csemI F fctx X) (fun sl cm w => MR sl cm w.1 ∧ Q cm w.2) ctx (.jump bc) [l] st st
      [.jump l] :=
  LowerTermOk.csemI (m := 0) (jump_csem F fctx (X.at 0) MR ctx bc l st)
    fun i hi => by simp only [List.mem_singleton] at hi; subst hi; rfl

end Backend.Proof.VCodeSemIDriverWitness
