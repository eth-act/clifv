import FV.E2E.LinkArmProgOsPR
import FV.E2E.LinkArmProgOsPWitness
import FV.E2E.LinkArmProphDetRWitness

/-!
# Witnesses for the call contracts on `ThmPDER` (`FV/E2E/LinkArmProgOsPR.lean`)

* `calleeOkPR_Lu`, `calleeTryOkPR_Lu`: on `LinkArmProphDetWitness.Lu` (a program with a call),
  the call and `try_call` contracts of call `n` at the `QR` states, with the induction hypothesis
  discharged by `thmPDER_LU`.
-/

namespace E2E.LinkArmProgOsPRWitness

open Backend Backend.Proof LinkArmProphDetWitness LinkArmProphDetRWitness LinkArmProgOsPWitness

theorem calleeOkPR_Lu (M : Nat) {g : Clif.Function} (hg : g ∈ Lu.P.funcs) {F G : BitVec 64 → Prop}
    {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : Lu.MachEntry (fun M _ => Lu.K M) M g F G ra s w₀) (P : Nat → BitVec 64 → BitVec 8)
    (R : Nat → Arm.ArmState) (n : Nat) :
    CalleeOkGP (QR (Lu.K M) P R n) F (Lu.K M) G s (CallAt (Lu.A g).fa (Lu.A g).base)
      (Lu.XPR (fun M _ => Lu.K M) M g F P R n) (Lu.hooks M) (Lu.A g).vcp.CallSite
      (GotV (Lu.A g).vcp) :=
  Lu.calleeOkPR Lu_ok (Lu.budget_K Lu_ok) (fun _ => thmPDER_LU _) hg he fun _ hq _ => hq

theorem calleeTryOkPR_Lu (M : Nat) {g : Clif.Function} (hg : g ∈ Lu.P.funcs)
    {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : Lu.MachEntry (fun M _ => Lu.K M) M g F G ra s w₀) (P : Nat → BitVec 64 → BitVec 8)
    (R : Nat → Arm.ArmState) (n : Nat) :
    CalleeTryOkGP (QR (Lu.K M) P R n) F (Lu.K M) G s (CallAt (Lu.A g).fa (Lu.A g).base)
      (Lu.XPR (fun M _ => Lu.K M) M g F P R n) (Lu.hooks M) (Lu.A g).vcp.TrySite
      (GotV (Lu.A g).vcp) :=
  Lu.calleeTryOkPR Lu_ok (Lu.budget_K Lu_ok) (fun _ => thmPDER_LU _) hg he fun _ hq _ => hq

end E2E.LinkArmProgOsPRWitness
