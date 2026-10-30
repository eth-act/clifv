import FV.E2E.LinkArmCallTab
import FV.E2E.LinkArmTableE

/-!
# A program call followed by no error returns (SEM1 #537, #680 (3), fix of #700, step 2)

* `mach_callsTo`: the step of `g`'s machine at a call of the function `h` of `P` (with `g`'s
  code laid out at the state's program base) is the linked call `pcall`;
* **`callsTo_ret`**: a call of `h` whose next state has no error is at depth `M' + 1` and the
  callee's run returns (first return `N'`): a non-returning callee is `junkAt`, an error. This is
  how the prefix-closed table (`TableOfE`) recovers a callee's return from the caller's run
  instead of presupposing it (`TableOf`, #700);
* **`tabUpToE_count`**: the prefix-closed count is unique when every call of the prefix is
  followed by a state without an error;
* **`tabUpToE_call_at`**: `tabUpTo_call_at` for `TableOfE`: at a call before the return without
  an error, the callee's `TableOfE` (no return needed) and, if it returns, its full table.
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

/-- **The prefix-closed count is unique** when every call of the prefix (with `g`'s code at the
program base) is followed by a state without an error: each callee returned (`callsTo_ret`), so
each call's count is pinned by the callee's full table (`tabUpTo_count`). -/
theorem tabUpToE_count {M : Nat} {g : Clif.Function} {s : Arm.ArmState}
    {b b' : Nat → Nat → BitVec 8} {k k' N e e' : Nat}
    (hpb : ∀ i < N, progBase (runX (L.mach M g) i s) = (L.A g).base)
    (herr : ∀ i < N, Arm.r .ERR (runX (L.mach M g) (i + 1) s) = .None)
    (h : L.TabUpToE M g s b k N e) (h' : L.TabUpToE M g s b' k' N e') : e = e' := by
  cases M with
  | zero => exact h.trans h'.symm
  | succ M =>
    obtain ⟨E, rfl, hE⟩ := h
    obtain ⟨E', rfl, hE'⟩ := h'
    refine sumTo_congr_calls N fun i hi hpc => ?_
    by_cases hcall : ∃ h, L.CallsTo g (runX (L.mach (M + 1) g) i s) h
    · obtain ⟨h, hch⟩ := hcall
      have hr := herr i hi
      rw [runX_add _ i 1] at hr
      obtain ⟨M', hM, N₁, hr₁, hm₁⟩ := L.callsTo_ret hch (hpb i hi) hr
      obtain rfl : M = M' := Nat.succ.inj hM
      obtain ⟨-, hle, -, ht₁⟩ := (hE i hi hpc).2 h hch
      obtain ⟨-, hle', -, ht₂⟩ := (hE' i hi hpc).2 h hch
      have := L.tabUpTo_count _ _ _ _ _ _ _ _ _ _ (ht₁ N₁ hr₁ hm₁) (ht₂ N₁ hr₁ hm₁)
      omega
    · have hn : ∀ h, ¬ L.CallsTo g (runX (L.mach (M + 1) g) i s) h := fun h hc => hcall ⟨h, hc⟩
      rw [(hE i hi hpc).1 hn, (hE' i hi hpc).1 hn]

/-- **The caller's prefix-closed table at a call before the return** (module doc): the count of
every prefix-closed table of the prefix before the call is `Σ_{j<n} E j`, the callee's slot bytes,
`slotted h ≤ E n`, **the callee's `TableOfE`** with the oracle advanced past the earlier entries
and the callee's own, and, if the callee returns, its run's full table with count `E n - slotted h`. -/
theorem tabUpToE_call_at {M : Nat} {g : Clif.Function} {s : Arm.ArmState} {ini : Clif.SlotInit}
    (htab : L.TableOfE (M + 1) g s ini) {i : Nat}
    (hnr : ∀ j < i + 1, ¬ L.RetAt g s (runX (L.mach (M + 1) g) j s))
    (herr : ∀ j < i + 1, Arm.r .ERR (runX (L.mach (M + 1) g) j s) = .None)
    (hpb : ∀ j < i, progBase (runX (L.mach (M + 1) g) j s) = (L.A g).base)
    (hcp : CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M + 1) g) i s)))
    {h : Clif.Function} (hct : L.CallsTo g (runX (L.mach (M + 1) g) i s) h) :
    ∃ E : Nat → Nat,
      (∀ e, L.TabUpToE (M + 1) g s ini.bytes ini.next i e →
        e = Clif.sumTo E (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i)) ∧
      (slotted h = 1 → ∀ a, L.SlotByte h (spv (runX (L.mach (M + 1) g) i s)) a →
        ini.bytes (ini.next + Clif.sumTo E
          (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) + 1) a =
          (runX (L.mach (M + 1) g) i s).mem (BitVec.ofNat 64 a)) ∧
      slotted h ≤ E (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) ∧
      L.TableOfE M h (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))
        ⟨ini.bytes, ini.next + Clif.sumTo E
          (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) + slotted h⟩ ∧
      ∀ N', RetOf (L.A h) (runX (L.mach (M + 1) g) i s)
          (runX (L.mach M h) N' (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))) →
        (∀ N'' < N', ¬ RetOf (L.A h) (runX (L.mach (M + 1) g) i s)
          (runX (L.mach M h) N'' (enterAt (L.A h) (runX (L.mach (M + 1) g) i s)))) →
        L.TabUpTo M h (enterAt (L.A h) (runX (L.mach (M + 1) g) i s)) ini.bytes
          (ini.next + Clif.sumTo E (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) +
            slotted h) N'
          (E (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) - slotted h) := by
  obtain ⟨e, E, -, hall⟩ := htab (i + 1) hnr herr
  have hpre : L.TabUpToE (M + 1) g s ini.bytes ini.next i
      (Clif.sumTo E (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i)) :=
    ⟨E, rfl, fun i' hi' => hall i' (by omega)⟩
  obtain ⟨h1, h2, h3, h4⟩ := (hall i (by omega) hcp).2 h hct
  refine ⟨E, fun e he => L.tabUpToE_count hpb (fun j hj => herr (j + 1) (by omega)) he hpre,
    h1, h2, fun N hN hE => h3 N (fun N'' hN'' hr => hN N'' hN'' ((L.retAt_enterAt_iff).2 hr)) hE,
    h4⟩

end LinkSys

end E2E
