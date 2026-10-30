import FV.E2E.LinkArmProphDetR
import FV.E2E.LinkArmProphDetWitness

/-!
# Witnesses for the linking statement with both prophecies (`FV/E2E/LinkArmProphDetR.lean`)

* `thmPDER_LU`: `ThmPDER` at every depth for `LinkArmProphDetWitness.Lu` (a program with a call,
  no non-interference); `thmPR_of_thmPDER_LU`: `ThmPDER.thmPR` on it;
* `thmPR_LU`: `Thm.thmPR` on it.
-/

namespace E2E.LinkArmProphDetRWitness

open Backend Backend.Proof LinkArmProphDetWitness

theorem thmPDER_LU (M : Nat) : Lu.ThmPDER (fun M _ => Lu.K M) M :=
  LinkSys.Thm.thmPDER_of_not_needNI Lu (LinkArmUProgWitness.noNI fun _ => True)
    (Lu.thm Lu_ok (Lu.budget_K Lu_ok) M)

theorem thmPR_of_thmPDER_LU : Lu.ThmPR (fun M _ => Lu.K M) 3 :=
  LinkSys.ThmPDER.thmPR Lu (thmPDER_LU 3)

theorem thmPR_LU (M : Nat) : Lu.ThmPR (fun M _ => Lu.K M) M :=
  LinkSys.Thm.thmPR Lu (Lu.thm Lu_ok (Lu.budget_K Lu_ok) M)

end E2E.LinkArmProphDetRWitness
