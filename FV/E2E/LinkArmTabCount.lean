import FV.E2E.LinkArmTableB

/-!
# The table count of a run prefix is unique (SEM1 #537, #680 (3) stage 2)

`TabUpTo M g s b k N e` fixes `e`: the count does not depend on the table `b` or its offset `k`
(they only constrain the slot bytes), and per call the callee's first return and its prefix count
are unique. `ThmPRB`'s count `e` (the CLIF counter's advance) is then the count of every table
of the run up to its return (`tabUpTo_count`), which ties the counts that `progCallPRB`
gives per call to the caller's table.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)

theorem sumTo_congr_calls {E E' : Nat → Nat} {Mm : Arm.ArmState → Arm.ArmState} {fa : FnAsm}
    {base : BitVec 64} {s : Arm.ArmState} :
    ∀ N, (∀ i < N, CallPc fa base (Arm.r .PC (runX Mm i s)) →
      E (callsBefore Mm fa base s i) = E' (callsBefore Mm fa base s i)) →
      Clif.sumTo E (callsBefore Mm fa base s N) = Clif.sumTo E' (callsBefore Mm fa base s N)
  | 0, _ => rfl
  | N + 1, h => by
    have ih := sumTo_congr_calls N fun i hi => h i (by omega)
    simp only [callsBefore]
    by_cases hc : CallPc fa base (Arm.r .PC (runX Mm N s))
    · simp only [hc, ↓reduceIte, Clif.sumTo, ih, h N (by omega) hc]
    · simp only [hc, ↓reduceIte, Nat.add_zero, ih]

/-- **The table count is unique** (module doc). -/
theorem tabUpTo_count : ∀ (M : Nat) (g : Clif.Function) (s : Arm.ArmState)
    (b b' : Nat → Nat → BitVec 8) (k k' N e e' : Nat),
    L.TabUpTo M g s b k N e → L.TabUpTo M g s b' k' N e' → e = e'
  | 0, _, _, _, _, _, _, _, _, _, h, h' => h.1.trans h'.1.symm
  | M + 1, g, s, b, b', k, k', N, e, e', h, h' => by
    obtain ⟨E, rfl, hE⟩ := h
    obtain ⟨E', rfl, hE'⟩ := h'
    refine sumTo_congr_calls N fun i hi hpc => ?_
    by_cases hcall : ∃ h, L.CallsTo g (runX (L.mach (M + 1) g) i s) h
    · obtain ⟨h, hch⟩ := hcall
      obtain ⟨-, hle, N₁, hr₁, hm₁, ht₁⟩ := (hE i hi hpc).2 h hch
      obtain ⟨-, hle', N₂, hr₂, hm₂, ht₂⟩ := (hE' i hi hpc).2 h hch
      have hN : N₁ = N₂ := by
        rcases Nat.lt_trichotomy N₁ N₂ with e | e | e
        · exact absurd hr₁ (hm₂ _ e)
        · exact e
        · exact absurd hr₂ (hm₁ _ e)
      subst hN
      have := tabUpTo_count M h _ b b' _ _ N₁ _ _ ht₁ ht₂
      omega
    · have hn : ∀ h, ¬ L.CallsTo g (runX (L.mach (M + 1) g) i s) h := fun h hc => hcall ⟨h, hc⟩
      rw [(hE i hi hpc).1 hn, (hE' i hi hpc).1 hn]

end LinkSys

end E2E
