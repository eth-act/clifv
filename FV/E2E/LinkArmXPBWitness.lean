import FV.E2E.LinkArmXPB
import FV.E2E.BackendWorldPRBWitness
import FV.E2E.LinkArmProphDetWitness

/-!
# Witnesses for `ExtSem.guardR` and the slot-byte program calls (`FV/E2E/ExtSemGuardR.lean`,
`FV/E2E/LinkArmXPB.lean`)

* `guardR_vacuous`: under a vacuous guard `guardR` is the guarded semantics itself (an undefined
  call stays undefined: the case `ExtSem.guard` answers ε, #680);
* `InvokedNWitness.hX_sCall_R`: `hX_guardRI` applies to the run from `sCall` (a call to a
  returning extern);
* `LinkArmTableBWitness.XPRB_Lu`: without program callees with slots, `XPRB` is `XPR` on `Lu`.
-/

namespace E2E.InvokedNWitness

open Backend Backend.Proof Backend.Proof.Driver CallPostExistsWitness

theorem guardR_vacuous (X : ExtSem) (d : Option String) (uses : List CV) (w : Arm.ArmState) :
    (X.guardR fun _ _ _ _ => True).call d uses w = X.call d uses w := by
  cases hx : X.call d uses w with
  | some r => exact ExtSem.guardR_of hx trivial
  | none =>
    cases hr : (X.guardR fun _ _ _ _ => True).call d uses w with
    | none => rfl
    | some r =>
      have := ExtSem.guardR_eq_of (X := X) (Q := fun _ _ _ _ => True)
        (fun h => absurd (fun _ => trivial) h) hr
      rw [hx] at this; cases this

/-- **`hX_guardRI` applies**: every `guardR`-guarded semantics meets the per-state contracts of
the run from `sCall`. -/
theorem hX_sCall_R (XI : ExtSemI) (Γ : Rel) (f : Clif.Function) (c : BitVec 64) :
    ∀ s n, ReachN envE PE sCall s n →
      XCallsOk (envE.only (Clif.Invoked envE PE s)) [extE] (RelW Γ f c)
        ((XI.guardRI (CallPostN envE PE sCall [extE] [] (RelW Γ f c) XI.sym)).at n) ∧
      XCallsIndOk (envE.only (Clif.Invoked envE PE s)) [] (RelW Γ f c)
        ((XI.guardRI (CallPostN envE PE sCall [extE] [] (RelW Γ f c) XI.sym)).at n) :=
  hX_guardRI XI noRetCall_sCall invokedRetOk_sCall

end E2E.InvokedNWitness

namespace E2E.LinkArmTableBWitness

open Backend Backend.Proof LinkArmProphDetWitness

theorem XPRB_Lu (M : Nat) (g : Clif.Function) (F : BitVec 64 → Prop)
    (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (n : Nat) (hN : ¬ Lu.NeedSlots) :
    Lu.XPRB (fun M _ => Lu.K M) M g F P R n = Lu.XPR (fun M _ => Lu.K M) M g F P R n :=
  Lu.XPRB_of_not_needSlots n hN

end E2E.LinkArmTableBWitness
