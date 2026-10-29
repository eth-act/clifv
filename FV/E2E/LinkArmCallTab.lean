import FV.E2E.LinkArmStage2Prog
import FV.E2E.LinkArmTabCount
import FV.E2E.RegLevelPrefixG

/-!
# The caller's table at a call before the return (SEM1 #537, #680 (3), stage 2 (P2))

At a call state of the activation reached before its return (the `Good` trace of
`regLevel_prefixPRSG`), the caller's table `TableOf M g s ini` covers the call: the prefix up to
and including the call has a table, whose call clause gives the callee's slot bytes (the memory at
the call), the callee's run up to its first return, and that run's table.

* `retAt_enterAt_iff`: a return of an entered callee is a return of its call (`RetOf`);
* **`noRetAt_upTo`**: no return of the activation up to a call state with the `Good` trace;
* **`tabUpTo_call_at`**: the caller's table at such a call (the prefix count before the call is
  `Σ_{j<n} E j`, the call clause);
* **`tableOf_callee`**: the callee run's table from the call clause (`TableOf` one level down).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **A return of an entered callee is a return of its call.** -/
theorem retAt_enterAt_iff {h : Clif.Function} {t x : Arm.ArmState} :
    L.RetAt h (enterAt (L.A h) t) x ↔ RetOf (L.A h) t x := by
  have h30 : xreg 30 (enterAt (L.A h) t) = Arm.r .PC t + 4 := by
    simp only [xreg, enterAt]
    rw [Arm.r_of_w_different (by decide), show (BitVec.ofNat 5 30) = 30#5 from rfl, Arm.r_of_w_same]
  have hsp : spv (enterAt (L.A h) t) = spv t := r_enterAt _ _ (by decide) (by decide)
  simp only [RetAt, RetOf, h30, hsp]

/-- **No return of the activation up to a call state** reached with the `Good` trace (no return
into `g`'s code but with the body `sp`), at the body `sp`, without error. -/
theorem noRetAt_upTo (hL : L.Ok) {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (hME : L.MachEntry κ M g F G ra s w₀) (hra : RaOk (L.A g) (ra - 4)) {i : Nat}
    (htr : ∀ j < i, ¬ PostCall (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach M g) j s)) ∨
      spOf (runX (L.mach M g) j s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af))
    (hsp : spOf (runX (L.mach M g) i s) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af))
    (herr : Arm.r .ERR (runX (L.mach M g) i s) = .None) :
    ∀ j < i + 1, ¬ L.RetAt g s (runX (L.mach M g) j s) := by
  have hroom := hME.stack.1.1
  have hfd := L.frameDrop_eq hL hg
  have hne : ∀ t, spOf t = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af) → spv t ≠ spv s := by
    intro t ht e
    have e' : spv s - BitVec.ofNat 64 (frameDrop (L.A g).af) = spv s := ht.symm.trans e
    have e2 := congrArg BitVec.toNat e'
    have hlt := (spv s).isLt
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at e2
    omega
  intro j hj
  rcases Nat.lt_or_ge j i with hji | hji
  · exact L.noRetAt_of hL hg hME hra (fun k hk0 hk hpc => (htr k hk).resolve_left (· hpc)) herr j hji
  · obtain rfl : j = i := by omega
    exact fun hri => hne _ hsp hri.2.2.2

/-- **The caller's table at a call before the return**: the count of every table of the prefix
before the call is `Σ_{j<n} E j` (`n` the call's index), and the call clause holds. -/
theorem tabUpTo_call_at {M : Nat} {g : Clif.Function} {s : Arm.ArmState} {ini : Clif.SlotInit}
    (htab : L.TableOf (M + 1) g s ini) {i : Nat}
    (hnr : ∀ j < i + 1, ¬ L.RetAt g s (runX (L.mach (M + 1) g) j s))
    (hcp : CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M + 1) g) i s)))
    {h : Clif.Function} (hct : L.CallsTo g (runX (L.mach (M + 1) g) i s) h) :
    ∃ E : Nat → Nat,
      (∀ e, L.TabUpTo (M + 1) g s ini.bytes ini.next i e →
        e = Clif.sumTo E (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i)) ∧
      (slotted h = 1 → ∀ a, L.SlotByte h (spv (runX (L.mach (M + 1) g) i s)) a →
        ini.bytes (ini.next + Clif.sumTo E
          (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) + 1) a =
          probeMem (L.A h).af (runX (L.mach (M + 1) g) i s) (BitVec.ofNat 64 a)) ∧
      slotted h ≤ E (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) ∧
      ∃ N', RetOf (L.A h) (runX (L.mach (M + 1) g) i s)
          (runX (L.mach M h) N' (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))) ∧
        (∀ N'' < N', ¬ RetOf (L.A h) (runX (L.mach (M + 1) g) i s)
          (runX (L.mach M h) N'' (enterAt (L.A h) (runX (L.mach (M + 1) g) i s)))) ∧
        L.TabUpTo M h (enterAt (L.A h) (runX (L.mach (M + 1) g) i s)) ini.bytes
          (ini.next + Clif.sumTo E (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) +
            slotted h) N'
          (E (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) - slotted h) := by
  obtain ⟨e, E, -, hall⟩ := htab (i + 1) hnr
  have hpre : L.TabUpTo (M + 1) g s ini.bytes ini.next i
      (Clif.sumTo E (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i)) :=
    ⟨E, rfl, fun i' hi' => hall i' (by omega)⟩
  obtain ⟨h1, h2, N', h3, h4, h5⟩ := (hall i (by omega) hcp).2 h hct
  exact ⟨E, fun e he => L.tabUpTo_count _ _ _ _ _ _ _ _ _ _ he hpre, h1, h2, N', h3, h4, h5⟩

/-- **The callee run's table from the call clause**: the run up to its first return has the
table of `ini'`, so the callee run has `ini'`'s table (`TableOf` one level down). -/
theorem tableOf_callee {M : Nat} {h : Clif.Function} {t : Arm.ArmState} {ini' : Clif.SlotInit}
    {N' e : Nat}
    (hret : RetOf (L.A h) t (runX (L.mach M h) N' (enterAt (L.A h) t)))
    (htab : L.TabUpTo M h (enterAt (L.A h) t) ini'.bytes ini'.next N' e) :
    L.TableOf M h (enterAt (L.A h) t) ini' := by
  intro N hN
  rcases Nat.lt_or_ge N' N with hlt | hle
  · exact absurd ((L.retAt_enterAt_iff).2 hret) (hN N' hlt)
  · exact L.tabUpTo_mono htab hle

end LinkSys

end E2E
