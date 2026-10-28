import FV.E2E.RegLevelCorrectPR
import FV.E2E.LinkArmProphThmWitness

/-!
# Witnesses for the register-prophecy reg-level theorem (`FV/E2E/RegLevelCorrectPR.lean`)

* `prophRegOkM_u0`: the run of `faC` from `u0` under the machine that stays put has the register
  prophecy `fun _ => u0`;
* `onCallPR_u0`: its state after 5 steps is an `OnCallPR` state of call 5 (both prophecies).
-/

namespace Backend.Proof.RegLevelCorrectPRWitness

open E2E E2E.LinkArmProphThmWitness

theorem prophRegOkM_u0 : ProphRegOkM 0x8000#64 id faC 0x1000#64 u0 fun _ => u0 :=
  fun i _ _ _ _ _ => by rw [runX_id]

theorem onCallPR_u0 :
    OnCallPR 16 0x8000#64 (prophOf id faC 0x1000#64 u0) (fun _ => u0) id faC 0x1000#64 u0 5 u0 :=
  onCallPR_of prophOk_u0 prophRegOkM_u0 ⟨5, runX_id 5 u0, callsBefore_u0 5⟩

end Backend.Proof.RegLevelCorrectPRWitness
