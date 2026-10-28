import FV.E2E.BackendWorldIR
import FV.E2E.RegLevelCorrectPRSWitness
import FV.E2E.IselSimIWitness

/-!
# Witnesses for the located reads (SEM1 #537, step 3p, `FV/E2E/RegLevelReadsIn.lean`)

* `worldPRSR_const`: `regLevelCorrect_worldPRSR` applies to `RegLevelCorrectUWitness`'s compiled
  function with a call (with the run's own prophecies): the run returns, and every state before
  the return has its reads located (`actReadsIn`);
* `a2_worldPRIR`: `backend_correct_worldPRIR` applies to `LinkWitness`'s compiled function `a2`.
-/

namespace Backend.Proof.RegLevelReadsInWitness

open Backend Backend.Proof E2E Backend.Proof.Driver RegLevelCorrectPRSWitness

open RegLevelCorrectUWitness RegLevelCorrectIWitness in
/-- **`regLevelCorrect_worldPRSR` applies to a compiled function with a call.** -/
theorem worldPRSR_const {X : ExtSem} {H : ArmHooks} {K : Nat} {fb : FnBin}
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
    ∃ n, ArmRet ra s (E2E.runX (ArmStepX X H fa) n s) ∧
      ∀ i < n, actReadsIn vc rf af fa fb base s X H K (fun _ => False) (fun _ _ => False)
        (E2E.runX (ArmStepX X H fa) i s) := by
  obtain ⟨hca, halloc, hemit, -⟩ := premises K X
  have hnt : vc.hasTryCall = false := by decide +kernel
  have hnl : vc.hasTls = false := by decide +kernel
  have e := frameWG_false K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af s
  obtain ⟨n, h, -, -, -, -, -, -, hrd⟩ := (regLevelCorrect_worldPRSR (XI := ExtSemI.const X)
    (G := fun _ => False)
    (gv := fun _ _ => False) hca halloc hemit hlayout hcov hent hres (fun _ h => h.elim)
    (prophOk_prophOf K (spv w₀) _ fa base s) (prophRegOkM_prophStOf (spv w₀) _ fa base s)
    (fun _ => by rw [e]; exact ((hC s).g _ s _ _).p _) (fun h => absurd h (by rw [hnt]; decide))
    (fun h => absurd h (by rw [hnl]; decide)) (by rw [e]; exact hbe) ρ₀).1 us vals w nc hret
  exact ⟨n, h, hrd⟩

end Backend.Proof.RegLevelReadsInWitness

namespace E2E.LinkWitness

open Backend Backend.Proof Backend.Proof.Driver

/-- **`backend_correct_worldPRIR` applies** to the program's compiled function `a2` (the entry
premises remain): the activations realising the returning run have their reads located. -/
theorem a2_worldPRIR {F : BitVec 64 → Prop} {c : BitVec 64} {K : Nat} {args : List Clif.Val}
    {cs : Clif.State} {w₀ : Arm.ArmState} (hce : ClifEntry fA2 args cs)
    (hrel : RelW ⟨F, fun _ => none, (A fA2).af.slotBase,
      (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase⟩ fA2 c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F fA2.sig args w₀)
    (htr : TrapsExplicit Clif.Rust.env (L F).P.bare cs) (fuel : Nat) :
    ∀ vals cm, Clif.runLoop Clif.Rust.env (L F).P.bare fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
          (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
          ActEntryPR (A fA2).vcp (A fA2).rf (A fA2).af (A fA2).fa (A fA2).fb K F G
            (ExtSemI.const Xb) H base ra Kp cc P R s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX ((ExtSemI.const Xb).at 0) H (A fA2).fa) n s) ∧
            ∀ i < n, actReadsIn (A fA2).vcp (A fA2).rf (A fA2).af (A fA2).fa (A fA2).fb base s
              ((ExtSemI.const Xb).at 0) H K G (GotV (A fA2).vcp)
              (runX (ArmStepX ((ExtSemI.const Xb).at 0) H (A fA2).fa) i s) := by
  have hL := L_ok (fun _ => True) (fun _ _ => trivial)
  have hA2 : fA2 ∈ P.funcs := by simp [P]
  intro vals cm hrun
  obtain ⟨us, outs, w, -, -, -, -, -, h⟩ := (backend_correct_worldPRIR (hL.subset fA2 hA2) a2_compiled
    a2_callsOne.1 a2_callsOne.2 (hL.covered fA2 hA2) (fun _ n _ => a2_xcalls _ _ _ n)
    (fun n b h => by cases h) rfl hce hrel hargs htr fuel).1 vals cm hrun
  refine ⟨us, outs, w, fun H G base ra Kp cc P R s he => ?_⟩
  obtain ⟨n, h1, -, h3⟩ := h H G base ra Kp cc P R s he
  exact ⟨n, h1, h3⟩

end E2E.LinkWitness
