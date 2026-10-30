import FV.E2E.LinkArmStage2R
import FV.E2E.LinkArmThmPRBRZeroWitness
import FV.E2E.LinkArmPlaceBWitness

/-!
# Witnesses for `LinkArmStage2R.lean`

* `thmPRBRL_ofR_Lsl`: `thmPRBRL_ofR` at depth `0` on the slotted test system `Lsl`, every
  premise discharged (`retOkPRB_Lsl`, `stage2PRBR_zero`, `countPRB_zero_Lsl`);
* `stage2Y_sZ`: `stage2Y_of_not_invoked` on the state `sZ` at `return` (a placed activation of
  `f0`, `LinkArmPlaceBWitness`): its run makes no call, so stage 2 holds at every count.
-/

namespace E2E.LinkSlotSysWitness

open Backend Backend.Proof Clif LinkArmPlaceBWitness

theorem thmPRBRL_ofR_Lsl : Lsl.ThmPRBRL (fun M _ => Lsl.K M) 0 :=
  Lsl.thmPRBRL_ofR Lsl_ok (Lsl.budget_K Lsl_ok) (fun h => absurd h (Nat.lt_irrefl 0))
    (fun h => absurd h (Nat.lt_irrefl 0)) (retOkPRB_Lsl 0) (Lsl.stage2PRBR_zero Lsl_ok)
    countPRB_zero_Lsl

/-- `Lsl` with `f0`'s program (stage 2's statement only reads `P.bare`). -/
def L0f : LinkSys := { Lsl with P := P0 }

theorem step_sZ_done : ∃ v m, step Env.empty L0f.P.bare sZ = .done v m := ⟨_, _, rfl⟩

theorem not_invoked_sZ (n : Nat) (nm : String) (vals : List Val) (m : Mem) :
    ¬ InvokedN Env.empty L0f.P.bare sZ n nm vals m := by
  rintro ⟨s, hr, h1, -⟩
  have hs : s = sZ := by
    clear h1
    induction hr with
    | refl => rfl
    | snoc _ hst ih =>
      subst ih
      obtain ⟨v, m, hd⟩ := step_sZ_done
      rw [hd] at hst
      cases hst
  subst hs
  exact absurd h1 (by decide)

/-- **`stage2Y_of_not_invoked` applies**: from `sZ` stage 2 holds at every count. -/
theorem stage2Y_sZ (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
    (c : BitVec 64) (Q : Arm.ArmState → Prop) (n : Nat) :
    L0f.Stage2Y κ M g F P R Env.empty sZ c Q n :=
  L0f.stage2Y_of_not_invoked (not_invoked_sZ n)

end E2E.LinkSlotSysWitness
