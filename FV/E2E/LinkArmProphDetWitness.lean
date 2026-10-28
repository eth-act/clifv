import FV.E2E.LinkArmProphDet
import FV.E2E.LinkArmProphThmWitness
import FV.E2E.LinkArmUProgWitness

/-!
# Witnesses for prophecy determinism (`FV/E2E/LinkArmProphDet.lean`)

* `prophStep_u0_u1`, `prophOk_u1`: two different states at the call `bl f` of
  `LinkArmProphThmWitness.faC` (`u1`: `u0` with `x0 := 7`) step in lock-step under the machine that
  stays put, so the prophecy of the run from `u0` (`prophOf`) is one of the run from `u1`;
  `callsBefore_u1`: their calls agree (`callsBefore_congr`);
* `thmPD_LU`: `ThmPD` at every depth for `LinkArmUProgWitness`'s two-function program (a call
  `f → h`, no non-interference needed), with its default callee runs (`std`) and the budget `K`;
  `thmP_of_thmPD_LU`: `ThmPD.thmP` on it.
-/

namespace E2E.LinkArmProphDetWitness

open Backend Backend.Proof LinkArmProphThmWitness

/-- `u0` with `x0 := 7`. -/
def u1 : Arm.ArmState := Arm.w (.GPR 0#5) 7#64 u0

theorem prophStep_u0_u1 (i : Nat) :
    ProphStep 16 0x8000#64 faC 0x1000#64 (runX id i u0) (runX id i u1) := by
  rw [runX_id, runX_id]
  refine ⟨?_, fun _ => ?_, fun _ _ _ _ => ?_⟩
  · simp only [u1]; rw [Arm.r_of_w_different (by simp)]
  · simp only [u1, spv]; rw [Arm.r_of_w_different (by simp)]
  · simp only [u1]; rw [Arm.ArmState.mem_w_eq_mem]

/-- **The prophecy of the run from `u0` is one of the run from `u1`.** -/
theorem prophOk_u1 : ProphOk 16 0x8000#64 id faC 0x1000#64 u1 (prophOf id faC 0x1000#64 u0) :=
  prophOk_prophOf_congr prophStep_u0_u1

theorem callsBefore_u1 : callsBefore id faC 0x1000#64 u1 5 = 5 := by
  rw [← callsBefore_congr (n := 5) (fun i _ => (prophStep_u0_u1 i).pc) 5 (Nat.le_refl 5),
    callsBefore_u0]

open LinkArmUProgWitness
/-- `LinkArmUProgWitness`'s system (code anywhere in `F = ⊤`) with its default callee runs. -/
def Lu : LinkSys := (LU fun _ => True).toLinkSys.std

instance : Lu.CrunOk :=
  (LU fun _ => True).toLinkSys.crunOk_std (L_ok _ fun _ _ => trivial)

theorem Lu_ok : Lu.Ok := (LinkArmUProgWitness.L_ok _ fun _ _ => trivial).withCrun _

/-- **`ThmPD` holds at every depth for a program with a call.** -/
theorem thmPD_LU (M : Nat) : Lu.ThmPD (fun M _ => Lu.K M) M :=
  LinkSys.Thm.thmPD_of_not_needNI Lu (LinkArmUProgWitness.noNI fun _ => True)
    (Lu.thm Lu_ok (Lu.budget_K Lu_ok) M)

theorem thmP_of_thmPD_LU : Lu.ThmP (fun M _ => Lu.K M) 3 :=
  LinkSys.ThmPD.thmP Lu (thmPD_LU 3)

end E2E.LinkArmProphDetWitness
