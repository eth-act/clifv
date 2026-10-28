import FV.E2E.LinkArmProgOsP
import FV.E2E.LinkArmProphDetEWitness

/-!
# Witnesses for `progOsP` (`FV/E2E/LinkArmProgOsP.lean`)

* `QR`: the state predicate of call `n` (masked registers of `R n`, `P n` below `sp`);
* `progOsP_Lu`: on `LinkArmProphDetWitness.Lu` (a program with a call), `progOsP`'s induction
  hypothesis (`thmPDE_LU`), budget and state premise are discharged: every program call site has
  the contract of call `n` at the `QR` states;
* `placeArgs_self_u0`: `placeArgs` of `u0`'s own `x0`, `x1` is `u0`.
-/

namespace E2E.LinkArmProgOsPWitness

open Backend Backend.Proof LinkArmProphDetWitness LinkArmProphDetEWitness

/-- The state predicate of call `n` of an activation of `g` at depth `M`. -/
def QR (K : Nat) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (n : Nat)
    (t : Arm.ArmState) : Prop :=
  (∀ f, MaskedReg f → Arm.r f t = Arm.r f (R n)) ∧ ∀ a, StackBelow K (spv t) a → t.mem a = P n a

theorem progOsP_Lu (M : Nat) {g : Clif.Function} (hg : g ∈ Lu.P.funcs) {F G : BitVec 64 → Prop}
    {s0 : Arm.ArmState} (himgF : ∀ a, Lu.Img a → F a) (himgG : ∀ a, Lu.Img a → G a)
    (himgS : ∀ a, Lu.Img a → s0.mem a = Lu.imgMem a) {info : CallInfo} {h : Clif.Function}
    (hsite : Lu.ProgSite g info h) (ctx : FnCtx) (P : Nat → BitVec 64 → BitVec 8)
    (R : Nat → Arm.ArmState) (n : Nat) :
    CallSoundCtlGP (QR (Lu.K M) P R n) F (Lu.K M) G s0 (CallAt (Lu.A g).fa (Lu.A g).base)
      (callExec (Lu.hooks M))
      (csemV (GotV (Lu.A g).vcp) F ctx (Lu.XPR (fun M _ => Lu.K M) M g F P R n)) (.call info)
      .next :=
  Lu.progOsP (κ := fun M _ => Lu.K M) Lu_ok (Lu.budget_K Lu_ok) (fun _ => thmPDE_LU _) hg himgF
    himgG himgS hsite ctx fun _ hq _ => hq

theorem placeArgs_self_u0 :
    placeArgs [.x 0, .x 1] ([.x 0, .x 1].map (regVal LinkArmProphThmWitness.u0))
      LinkArmProphThmWitness.u0 = LinkArmProphThmWitness.u0 :=
  placeArgs_self _ _

end E2E.LinkArmProgOsPWitness
