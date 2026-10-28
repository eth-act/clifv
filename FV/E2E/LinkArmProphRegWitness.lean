import FV.E2E.LinkArmProphReg
import FV.E2E.LinkArmProphDetWitness

/-!
# Witnesses for the register prophecy (`FV/E2E/LinkArmProphReg.lean`)

* `regOverlay_x19`, `regOverlay_sp`: the overlay of `u19` (`u0` with `x19 := 5`) onto `u0` takes
  `x19` from `u19` and keeps `u0`'s `sp`; `regOverlay_ne`: it changes `x19` of `u20` (`x19 := 6`);
* `prophRegOk_u0`: the register prophecy of the run from `u0` (`prophStOf`) holds;
  `prophStOf_u0`: call number 5 of that run is `u0` itself;
* `XPR_call_Lu`: on `LinkArmProphDetWitness.Lu`, with the world's own registers `XPR` is `XP`.
-/

namespace E2E.LinkArmProphRegWitness

open Backend Backend.Proof LinkArmProphThmWitness LinkArmProphDetWitness

/-- `u0` with `x19 := 5`. -/
def u19 : Arm.ArmState := Arm.w (.GPR 19#5) 5#64 u0

theorem maskedReg_x19 : MaskedReg (.GPR 19#5) := by simp only [MaskedReg, Masked]; decide

theorem not_maskedReg_sp : ¬ MaskedReg (.GPR 31#5) := by simp only [MaskedReg, Masked]; decide

theorem regOverlay_x19 : Arm.r (.GPR 19#5) (regOverlay u19 u0) = 5#64 := by
  rw [r_regOverlay_in maskedReg_x19, u19, Arm.r_of_w_same]

theorem regOverlay_sp : Arm.r (.GPR 31#5) (regOverlay u19 u0) = Arm.r (.GPR 31#5) u0 :=
  r_regOverlay_out not_maskedReg_sp

/-- `u0` with `x19 := 6`. -/
def u20 : Arm.ArmState := Arm.w (.GPR 19#5) 6#64 u0

/-- The overlay changes `x19` of `u20`. -/
theorem regOverlay_ne : Arm.r (.GPR 19#5) (regOverlay u19 u20) ≠ Arm.r (.GPR 19#5) u20 := by
  rw [r_regOverlay_in maskedReg_x19, u19, u20, Arm.r_of_w_same, Arm.r_of_w_same]
  decide

theorem prophRegOk_u0 :
    ProphRegOk 0x8000#64 id faC 0x1000#64 u0 (prophStOf id faC 0x1000#64 u0) :=
  prophRegOk_prophStOf _ _ _ _ _

theorem prophStOf_u0 : prophStOf id faC 0x1000#64 u0 5 = u0 := by
  have hc : CallPc faC 0x1000#64 (Arm.r .PC (runX id 5 u0)) := by
    rw [runX_id]; exact callPc_u0 0
  have := prophStOf_call hc
  rwa [callsBefore_u0, runX_id] at this

theorem XPR_call_Lu (g : Clif.Function) (F : BitVec 64 → Prop) (P : Nat → BitVec 64 → BitVec 8)
    (n : Nat) (d : Option String) (uses : List CV) (w : Arm.ArmState) :
    (Lu.XPR (fun M _ => Lu.K M) 2 g F P (fun _ => w) n).call d uses w =
      (Lu.XP (fun M _ => Lu.K M) 2 g F P n).call d uses w :=
  Lu.XPR_call_self g F P _ n d uses fun _ _ => rfl

end E2E.LinkArmProphRegWitness
