import FV.E2E.RegLevelCorrectP
import FV.E2E.RegLevelCorrectIWitness

/-!
# Witnesses for the refined call contract (`FV/E2E/RegLevelCorrectP.lean`)

* `onCallP_entry`: the entry state of every run is `OnCallP` with count `0` and the run's own
  prophecy `prophOf`;
* `worldP_const`: `regLevelCorrect_worldP` applies to `RegLevelCorrectUWitness`'s compiled
  function with a call, with the run's own prophecy (`prophOk_prophOf`) and one external
  semantics for every call index.
-/

namespace Backend.Proof.RegLevelCorrectPWitness

open Backend Backend.Proof E2E Backend.Proof.Driver

theorem onCallP_entry (K : Nat) (c : BitVec 64) (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm)
    (base : BitVec 64) (s : Arm.ArmState) :
    OnCallP K c (prophOf Mm fa base s) Mm fa base s 0 s :=
  onCallP_of_prophOk (prophOk_prophOf K c Mm fa base s) ⟨0, rfl, rfl⟩

open RegLevelCorrectUWitness RegLevelCorrectIWitness in
/-- **`regLevelCorrect_worldP` applies to a compiled function with a call**, with the machine
run's own prophecy. -/
theorem worldP_const {X : ExtSem} {H : ArmHooks} {K : Nat} {fb : FnBin}
    (hlayout : fa.layout = .ok fb) (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vc)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af s) K X H vc.CallSite)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) {w₀ : Arm.ArmState}
    (hbe : BodyEntryW (frameW K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af s)
      vc.EntryArg af s w₀) (ρ₀ : Nat → CV) (us : List (Reg × Reg)) (vals : List CV)
    (w : Arm.ArmState) (nc : Nat)
    (hret : VRetFrom vc (csemVI (fun _ _ => False) (frameWG K (RAFrame.compute vc rf).intBase
        (RAFrame.compute vc rf).size af (fun _ => False) s) ⟨fa.k, af.slotBase⟩ (ExtSemI.const X))
        ⟨0, 0, ρ₀, (w₀, 0)⟩ us vals (w, nc)) :
    ∃ n, ArmRet ra s (E2E.runX (ArmStepX X H fa) n s) := by
  obtain ⟨hca, halloc, hemit, -⟩ := premises K X
  have hnt : vc.hasTryCall = false := by decide +kernel
  have hnl : vc.hasTls = false := by decide +kernel
  have e := frameWG_false K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af s
  obtain ⟨n, h, -⟩ := (regLevelCorrect_worldP (XI := ExtSemI.const X) (G := fun _ => False)
    (gv := fun _ _ => False) hca halloc hemit hlayout hcov hent hres (fun _ h => h.elim)
    (prophOk_prophOf K (spv w₀) _ fa base s)
    (fun _ => by rw [e]; exact ((hC s).g _ s _ _).p _) (fun h => absurd h (by rw [hnt]; decide))
    (fun h => absurd h (by rw [hnl]; decide)) (by rw [e]; exact hbe) ρ₀).1 us vals w nc hret
  exact ⟨n, h⟩

end Backend.Proof.RegLevelCorrectPWitness
