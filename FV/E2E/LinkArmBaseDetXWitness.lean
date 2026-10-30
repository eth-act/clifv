import FV.E2E.LinkArmBaseDetX
import FV.E2E.LinkArmProphDetWitness

/-!
# Witnesses for base hooks that do not observe return addresses (`LinkArmBaseDetX.lean`)

* `okDX_Lu`: `OkDX` for `LinkArmProphDetWitness.Lu` (a program with a call, no non-interference);
* `hookDetX_id_any`: the hooks that change nothing satisfy `HookDetX` at every destination;
* `lrByte_fp`: the byte 8 above `x29` (the current record's saved LR) is an `LRByte`.
-/

namespace E2E.LinkArmBaseDetXWitness

open Backend Backend.Proof LinkArmProphDetWitness

theorem okDX_Lu : Lu.OkDX :=
  LinkSys.Ok.okDX_of_not_needNI Lu_ok (LinkArmUProgWitness.noNI fun _ => True)

theorem hookDetX_id_any : HookDetX ⟨fun _ s => s, fun _ _ s => s⟩ fun _ => True :=
  hookDetX_id _

theorem lrByte_fp (s : Arm.ArmState) : LRByte s (Arm.r (.GPR 29#5) s + 8#64) :=
  ⟨0, 0, by decide, by simp [fpChain]⟩

end E2E.LinkArmBaseDetXWitness
