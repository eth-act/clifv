import FV.E2E.LinkArmTableE

/-!
# A program call followed by no error returns (SEM1 #537, #680 (3), fix of #700, step 2)

* `mach_callsTo`: the step of `g`'s machine at a call of the function `h` of `P` (with `g`'s
  code laid out at the state's program base) is the linked call `pcall`;
* **`callsTo_ret`**: a call of `h` whose next state has no error is at depth `M' + 1` and the
  callee's run returns (first return `N'`): a non-returning callee is `junkAt`, an error. This is
  how the prefix-closed table (`TableOfE`) recovers a callee's return from the caller's run
  instead of presupposing it (`TableOf`, #700).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)

/-- **A call of a function of `P` is the linked call.** -/
theorem mach_callsTo {M : Nat} {g h : Clif.Function} {t : Arm.ArmState}
    (hc : L.CallsTo g t h) (hpb : progBase t = (L.A g).base) : L.mach M g t = L.pcall M h t := by
  show ArmStepX L.Xb (L.hooks M) (L.A g).fa t = _
  rcases hc with ⟨n, hins, hn⟩ | ⟨⟨x, hins⟩, hcal⟩
  · rw [← hpb] at hins
    simp only [ArmStepX, hins, LinkSys.hooks_call, LinkSys.callHook]
    rw [hn]
  · rw [← hpb] at hins
    simp only [ArmStepX, hins, LinkSys.hooks_call, LinkSys.callHook]
    rw [hcal]

/-- **A call followed by no error returns** (module doc). -/
theorem callsTo_ret {M : Nat} {g h : Clif.Function} {t : Arm.ArmState}
    (hc : L.CallsTo g t h) (hpb : progBase t = (L.A g).base)
    (herr : Arm.r .ERR (L.mach M g t) = .None) :
    ∃ M', M = M' + 1 ∧ ∃ N', RetOf (L.A h) t (runX (L.mach M' h) N' (enterAt (L.A h) t)) ∧
      ∀ N'' < N', ¬ RetOf (L.A h) t (runX (L.mach M' h) N'' (enterAt (L.A h) t)) := by
  rw [L.mach_callsTo hc hpb] at herr
  cases M with
  | zero => exact absurd herr (by simp [pcall, junkAt, Arm.r_of_w_same])
  | succ M' =>
    refine ⟨M', rfl, ?_⟩
    simp only [pcall, linkedCall] at herr
    split at herr
    · rename_i hex
      obtain ⟨hN, hmin⟩ := firstNat_spec _ hex
      exact ⟨_, hN, hmin⟩
    · exact absurd herr (by simp [junkAt, Arm.r_of_w_same])

end LinkSys

end E2E
