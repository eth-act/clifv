module

public import FV.E2E.LinkArmProphDetE
public import FV.E2E.LinkArmProphDetWitness

@[expose] public section

/-!
# Witnesses for entry-level prophecy determinism (`FV/E2E/LinkArmProphDetE.lean`)

* `thmPDE_LU`: `ThmPDE` at every depth for `LinkArmProphDetWitness.Lu` (a program with a call, no
  non-interference); `thmP_of_thmPDE_LU`: `ThmPDE.thmP` on it;
* `entryAgree_u0_u1`: `u0` and `u1` (`x0 := 7`) do not agree at the entry (`x0` is masked), `u0`
  agrees with itself.
-/

namespace E2E.LinkArmProphDetEWitness

open Backend Backend.Proof LinkArmProphThmWitness LinkArmProphDetWitness

theorem thmPDE_LU (M : Nat) : Lu.ThmPDE (fun M _ => Lu.K M) M :=
  LinkSys.Thm.thmPDE_of_not_needNI Lu (LinkArmUProgWitness.noNI fun _ => True)
    (Lu.thm Lu_ok (Lu.budget_K Lu_ok) M)

theorem thmP_of_thmPDE_LU : Lu.ThmP (fun M _ => Lu.K M) 3 :=
  LinkSys.ThmPDE.thmP Lu (thmPDE_LU 3)

theorem entryAgree_u0 : EntryAgree 16 u0 u0 := EntryAgree.refl 16 u0

theorem not_entryAgree_u1_u0 : ¬ EntryAgree 16 u1 u0 := by
  intro ⟨h, _⟩
  have := h (.GPR 0#5) (by simp only [Masked]; decide) (by simp) (by simp)
  rw [u1, Arm.r_of_w_same, u0, Arm.r_of_w_different (by simp),
    Arm.r_of_w_different (by simp)] at this
  simp [Arm.r, Arm.read_base_gpr, Arm.ArmState.default, Arm.read_store] at this

end E2E.LinkArmProphDetEWitness
