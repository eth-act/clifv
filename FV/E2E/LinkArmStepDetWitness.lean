import FV.E2E.LinkArmStepDet
import FV.E2E.LinkArmBaseDetWitness

/-!
# Witnesses for the two-state step (`FV/E2E/LinkArmStepDet.lean`)

* `stepiEvs_u0`: the state `u0` (`LinkArmProphThmWitness`, no program loaded) executes no
  instruction, so its step reads nothing;
* `stEqOut_stepi_u0`: `Arm.stepi` from `u0` and from `u0` with one more byte at `0x7ff0`
  (`LinkArmBaseDetWitness.sB`) gives states equal but for that byte;
* `stEqOut_armStepX_u0`: likewise one step of `faC`'s machine (`bl f`, a hooked line) with the
  hooks that change nothing.
-/

namespace E2E.LinkArmStepDetWitness

open Arm Backend Backend.Proof LinkArmProphThmWitness LinkArmBaseDetWitness

theorem stepiEvs_u0 : stepiEvs u0 = [] := by
  unfold stepiEvs
  split
  · split
    · rfl
    · rename_i i hf
      exfalso
      simp [u0, fetch_inst, Arm.w_program, ArmState.default, Map.find?] at hf
  · rfl

theorem stEqOut_stepi_u0 :
    StEqOut (fun x => x = 0x7ff0#64) (stepi u0) (stepi (sB u0)) :=
  stEqOut_stepi (stEqOut_u u0) (by rw [stepiEvs_u0]; intro e he; simp at he)

theorem stEqOut_armStepX_u0 (X : ExtSem) :
    StEqOut (fun x => x = 0x7ff0#64) (ArmStepX X ⟨fun _ s => s, fun _ _ s => s⟩ faC u0)
      (ArmStepX X ⟨fun _ s => s, fun _ _ s => s⟩ faC (sB u0)) :=
  stEqOut_armStepX_call (stEqOut_u u0) (fun _ => stEqOut_u u0) (fun _ _ => stEqOut_u u0)
    (by rw [stepiEvs_u0]; intro e he; simp at he)

end E2E.LinkArmStepDetWitness
