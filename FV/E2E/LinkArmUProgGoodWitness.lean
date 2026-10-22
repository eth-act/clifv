import FV.E2E.LinkArmUProgGood
import FV.E2E.LinkArmUProgNIWitness

/-!
# Non-vacuity of the per-state facts of the whole-program run with unwinding (S10g, #404)

`backend_correct_program_budgetUG'` applied to the linked program with unwinding of
`FV/E2E/LinkArmUProgNIWitness.lean` (`LinkWitness.L`, 18 compiled functions, its linking needs
non-interference): every premise but the entry state's and the run's outcome holds.
-/

namespace E2E.LinkArmUProgGoodWitness

open Backend Backend.Proof Backend.Proof.Driver LinkWitness LinkArmUProgNIWitness

/-- **`backend_correct_program_budgetUG'` applies** to this system (with `NeedNI`): for every entry
state of `f` and every returning, trapping or unwinding run, every state of the linked machine's
run with unwinding (and of the activations nested through its calls) whose step ends without
error has the per-state facts (`RunGoodLU`). -/
theorem budgetUG'_applies (F : BitVec 64 → Prop) (hF : ∀ a, Img P A a → F a) :
    (LUN F).NeedNI → ∀ (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
      {cs : Clif.State},
      AbiEntry ((LUN F).A fF).fb ((LUN F).A fF).base ra s →
      StackAvail ((LUN F).K M) ((LUN F).A fF).af s →
      (LUN F).F = frameWG ((LUN F).K M)
        (RAFrame.compute ((LUN F).A fF).vcp ((LUN F).A fF).rf).intBase
        (RAFrame.compute ((LUN F).A fF).vcp ((LUN F).A fF).rf).size ((LUN F).A fF).af
        (LUN F).Img s →
      (∀ a, (LUN F).Img a → ¬ StackBelow (frameDrop ((LUN F).A fF).af + (LUN F).K M) (spv s) a) →
      (∀ a, (LUN F).Img a → s.mem a = (LUN F).imgMem a) →
      BodyEntry ((LUN F).A fF).af s w₀ → ArgsIn fF.sig args s → ClifEntry fF args cs →
      StackArgsAvoid (LUN F).Img fF.sig args s →
      Rel.holds ⟨(LUN F).F, (LUN F).syms, ((LUN F).A fF).af.slotBase,
        (RAFrame.compute ((LUN F).A fF).vcp ((LUN F).A fF).rf).intBase⟩ fF cs.frame.slots
        cs.mem w₀ →
      ((LUN F).NeedSlots → (LUN F).PlaceAt cs.mem (spv w₀)) →
      TrapsExplicitX ((LUN F).stdX.envRX M fF) (LUN F).P.bare cs →
      ((∃ vals cm, Clif.runLoopX (LUN F).envX (LUN F).P (M + 1) cs.toX = .returned vals cm) ∨
        (∃ c, Clif.runLoopX (LUN F).envX (LUN F).P (M + 1) cs.toX = .trapped c) ∨
        (∃ e cm, Clif.runLoopX (LUN F).envX (LUN F).P (M + 1) cs.toX = .unwound e cm)) →
      (LUN F).RunGoodLU M fF s := by
  intro _ M ra s w₀ args cs hent hres hFe hgfree himg hbe hargs hcs hsav hrel hpl htr hout
  obtain ⟨hL, hU, hNI, hκ, hfF, -⟩ := budgetU'_applies F hF
  exact backend_correct_program_budgetUG' (LUN F) hL hU hNI hκ hfF M hent hres hFe hgfree himg hbe
    hargs hcs hsav hrel hpl htr hout

/-- The premise `NeedNI` of `budgetUG'_applies` holds (the linking needs non-interference). -/
theorem budgetUG'_needNI : (LUN F0).NeedNI := needNI

end E2E.LinkArmUProgGoodWitness
