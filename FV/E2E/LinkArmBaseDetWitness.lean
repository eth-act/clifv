import FV.E2E.LinkArmBaseDet
import FV.E2E.LinkArmProphDetWitness

/-!
# Witnesses for deterministic base hooks (`FV/E2E/LinkArmBaseDet.lean`)

* `okD_Lu`: `OkD` for `LinkArmProphDetWitness.Lu` (a program with a call, no non-interference);
* `hookDet_id_any`: the hooks that change nothing are deterministic at every destination;
* `stEqOut_u`: two states differing in one byte below `sp` are `StEqOut` that byte.
-/

namespace E2E.LinkArmBaseDetWitness

open Backend Backend.Proof LinkArmProphDetWitness

theorem okD_Lu : Lu.OkD :=
  LinkSys.Ok.okD_of_not_needNI Lu_ok (LinkArmUProgWitness.noNI fun _ => True)

theorem hookDet_id_any : HookDet ⟨fun _ s => s, fun _ _ s => s⟩ fun _ => True :=
  hookDet_id _

/-- `s` with the byte at `0x7ff0` set to `1`. -/
noncomputable def sB (s : Arm.ArmState) : Arm.ArmState := Backend.Proof.overlay (fun x => x = 0x7ff0#64) (fun _ => 1#8) s

theorem stEqOut_u (s : Arm.ArmState) : StEqOut (fun x => x = 0x7ff0#64) s (sB s) :=
  ⟨fun f => (r_overlay f s).symm, rfl, fun a ha => (mem_overlay_out (R := fun x => x = 0x7ff0#64) (P := fun _ => 1#8) (s := s) (a := a) ha).symm⟩

end E2E.LinkArmBaseDetWitness
