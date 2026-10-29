module

public import FV.E2E.RegLevelCorrectC
public import FV.E2E.RegLevelCorrectIWitness

@[expose] public section

/-!
# Witnesses for the count-indexed register-level theorem (`FV/E2E/RegLevelCorrectC.lean`)

* `countIn`: on the successor machine of `Nat` from `0`, the even states among the first `5`
  are `3` (`countIn_add`), none of the states `≥ 7` among the first `4` from `7`
  (`countIn_zero_of`), exactly one `= 2` among the first `5` (`countIn_one_of`);
* `RealizesCP.countedRun`: the identity machine (`realizes_any`) at every index;
* `onCall_zero`: the entry state is `OnCall` with count `0`;
* `worldC_const`: `regLevelCorrect_worldC` applies to `RegLevelCorrectUWitness`'s compiled
  function with a call, with one external semantics for every call index, the contracts given
  only along the run (`CalleeOkG.p`).
-/

namespace Backend.Proof.RegLevelCorrectCWitness

open Backend Backend.Proof E2E Backend.Proof.Driver

theorem count_even : countIn (fun n : Nat => n % 2 = 0) Nat.succ 0 (2 + 3) =
    countIn (fun n : Nat => n % 2 = 0) Nat.succ 0 2 +
      countIn (fun n : Nat => n % 2 = 0) Nat.succ (iterN Nat.succ 2 0) 3 :=
  countIn_add _ _ _ 2 3

theorem iterN_succ_nat : ∀ (i s : Nat), iterN Nat.succ i s = s + i
  | 0, s => rfl
  | i + 1, s => by
    show iterN Nat.succ i (s + 1) = s + (i + 1)
    rw [iterN_succ_nat i (s + 1)]; omega

theorem count_none : countIn (fun n : Nat => n < 7) Nat.succ 7 4 = 0 :=
  countIn_zero_of fun i _ => by rw [iterN_succ_nat]; omega

theorem count_one : countIn (fun n : Nat => n = 2) Nat.succ 0 5 = 1 :=
  countIn_one_of (i0 := 2) (by omega) (by rw [iterN_succ_nat])
    fun i _ hi => by rw [iterN_succ_nat]; omega

theorem countIn_true {S : Type} (step : S → S) (s : S) :
    ∀ n, countIn (fun _ => True) step s n = n
  | 0 => rfl
  | n + 1 => by
    show countIn (fun _ => True) step s n + ind True = n + 1
    rw [countIn_true step s n]; simp [ind]

/-- The identity machine, every state counted, with `opCalls` steps per segment, realises the
counted semantics on its run. -/
theorem countedRun_any (vc : VCode) (rf : RFunc) (sem : Nat → ISem CV Arm.ArmState) :
    Realizes vc rf (ISem.counted sem) ckeep (stepC (fun _ : Unit => True) id)
      (fun p c => True ∧ p.2 = c.world.2 ∧ ∃ i, p = iterN (stepC (fun _ : Unit => True) id) i ((), 0))
      (fun _ => True) :=
  RealizesCP.countedRun (Q := fun _ _ => True) (T := fun _ => True) (P := fun _ _ => True)
    (fun _ _ c c' _ _ hs => ⟨opCalls vc c, c', hs, trivial, fun _ _ => trivial, countIn_true _ _ _⟩)
    fun _ => trivial

/-- The entry state of a run is `OnCall` with count `0`. -/
theorem onCall_zero (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm) (base : BitVec 64)
    (s : Arm.ArmState) : OnCall Mm fa base s 0 s := ⟨0, rfl, rfl⟩

open RegLevelCorrectUWitness RegLevelCorrectIWitness in
/-- **`regLevelCorrect_worldC` applies to a compiled function with a call** with one external
semantics for every call index, the contracts restricted to the run (`CalleeOkG.p`). -/
theorem worldC_const {X : ExtSem} {H : ArmHooks} {K : Nat} {fb : FnBin}
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
  obtain ⟨n, h, -⟩ := (regLevelCorrect_worldC (XI := ExtSemI.const X) (G := fun _ => False)
    (gv := fun _ _ => False) hca halloc hemit hlayout hcov hent hres (fun _ h => h.elim)
    (fun _ => by rw [e]; exact ((hC s).g _ s _ _).p _) (fun h => absurd h (by rw [hnt]; decide))
    (fun h => absurd h (by rw [hnl]; decide)) (by rw [e]; exact hbe) ρ₀).1 us vals w nc hret
  exact ⟨n, h⟩

end Backend.Proof.RegLevelCorrectCWitness
