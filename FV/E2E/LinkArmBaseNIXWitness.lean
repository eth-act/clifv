import FV.E2E.LinkArmBaseNIX
import FV.E2E.LinkArmProphDetWitness

/-!
# Witnesses for `LinkArmBaseNIX.lean` (#704, #705)

* `okDNX_Lu`: `OkDNX` for `LinkArmProphDetWitness.Lu` (a program with a call, no non-interference);
* `hookNIX_id_any`: the hooks that change nothing satisfy `HookNIX` at every destination and every
  exterior;
* `thmPDERX29_LU`: `ThmPDERX29` at every depth for `Lu` (`Thm.thmPDERX29_of_not_needNI`), and
  `ThmPDERX29.thmPR` on it.
-/

namespace E2E.LinkArmBaseNIXWitness

open Backend Backend.Proof LinkArmProphDetWitness

theorem okDNX_Lu : Lu.OkDNX :=
  LinkSys.Ok.okDNX_of_not_needNI Lu_ok (LinkArmUProgWitness.noNI fun _ => True)

theorem hookNIX_id_any : HookNIX ⟨fun _ s => s, fun _ _ s => s⟩ (fun _ => True) (fun _ => True) :=
  hookNIX_id _ _

theorem thmPDERX29_LU (M : Nat) : Lu.ThmPDERX29 (fun M _ => Lu.K M) M :=
  LinkSys.Thm.thmPDERX29_of_not_needNI Lu (LinkArmUProgWitness.noNI fun _ => True)
    (Lu.thm Lu_ok (Lu.budget_K Lu_ok) M)

theorem thmPR_of_thmPDERX29_LU : Lu.ThmPR (fun M _ => Lu.K M) 3 :=
  LinkSys.ThmPDERX29.thmPR Lu (thmPDERX29_LU 3)

end E2E.LinkArmBaseNIXWitness
