import FV.E2E.DeadCleanupExecGot
import FV.E2E.LinkArmIniOf

/-!
# The oracle route's scope conditions with no code outside the program (SEM1 #537)

For the closed base environment (`closedBase`: no extern outside the program, the call hook
skips the instruction and keeps the state otherwise) two of the three scope conditions of
`InitOkR` hold for every system the proof instantiates (`sysS`): `baseRetOk_closed` (no base
extern returns) and `hooksKeep_closed`. The third, `RetCount`, is a fact of the program's
declarations, decided by `retCountB`: `retCount_of_B` (on the computable system `sys`).
-/

namespace E2E.DeadCleanupExecBytes

open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary

/-- **No base extern returns** with no code outside the program. -/
theorem baseRetOk_closed (I : LinkInput) (f : Clif.Function) (r : Arm.ArmState)
    (S : BitVec 64 → Prop) : (sysS I closedBase f r S).BaseRetOk := by
  intro n G hG
  change Clif.Env.empty.extern n = some G at hG
  simp [Clif.Env.empty] at hG

/-- **The closed base's hooks keep an error state and the loaded program.** -/
theorem hooksKeep_closed (I : LinkInput) (f : Clif.Function) (r : Arm.ArmState)
    (S : BitVec 64 → Prop) : (sysS I closedBase f r S).HooksKeep :=
  ⟨fun _ s h => by
      show Arm.r .ERR (Arm.w .PC (Arm.r .PC s + 4) s) ≠ .None
      rw [Arm.r_of_w_different (by simp)]; exact h,
    fun _ _ _ h => h, fun _ s => Arm.w_program, fun _ _ _ => rfl⟩

/-- `baseRetOk_closed` on the computable system `sys` (the condition reads only the base). -/
theorem baseRetOk_closedSys (I : LinkInput) : (sys I closedBase).BaseRetOk := by
  intro n G hG
  change Clif.Env.empty.extern n = some G at hG
  simp [Clif.Env.empty] at hG

/-- `hooksKeep_closed` on the computable system `sys`. -/
theorem hooksKeep_closedSys (I : LinkInput) : (sys I closedBase).HooksKeep :=
  ⟨fun _ s h => by
      show Arm.r .ERR (Arm.w .PC (Arm.r .PC s + 4) s) ≠ .None
      rw [Arm.r_of_w_different (by simp)]; exact h,
    fun _ _ _ h => h, fun _ s => Arm.w_program, fun _ _ _ => rfl⟩

/-- `retCountB` reads only the program. -/
theorem retCountB_sysS (I : LinkInput) (B : BaseEnv) (f : Clif.Function) (r : Arm.ArmState)
    (S : BitVec 64 → Prop) (g : Clif.Function) :
    (sysS I B f r S).retCountB g = (sys I B).retCountB g := rfl

/-- **`RetCount` from the decided check** on the computable system `sys`. -/
theorem retCount_of_B {I : LinkInput} {B : BaseEnv} {f : Clif.Function} {r : Arm.ArmState}
    {S : BitVec 64 → Prop} (h : (prog I).funcs.all ((sys I B).retCountB ·) = true) :
    ∀ g ∈ (sysS I B f r S).P.funcs, (sysS I B f r S).RetCount g := fun g hg =>
  LinkSys.retCountB_sound _ (by rw [retCountB_sysS]; exact List.all_eq_true.mp h g hg)

end E2E.DeadCleanupExecBytes
