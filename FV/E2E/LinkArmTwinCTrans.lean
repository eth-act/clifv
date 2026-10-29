module

public import FV.E2E.LinkArmTwinC

@[expose] public section

/-!
# Call-restricted twins compose (SEM1 #537, #713, determinism step)

The determinism step compares the callee runs at a program call of two locked caller runs. What
the induction on the depth provides is the twin of each of them with the canonical callee run
(`CallTwinC`: the run from a caller state `t` and from `canon h uses w`); the two are twins of each
other by symmetry and transitivity:

* `noRetAt_twinC'`: no return of the twin before the first return of the run (the converse of
  `noRetAt_twinC`);
* **`TwinBaseC.trans`**, **`TwinC.trans`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)

/-- **No return of the twin before the run's first return.** -/
theorem noRetAt_twinC' {M : Nat} {g : Clif.Function} {s s₀ : Arm.ArmState}
    (h : L.TwinBaseC M g s s₀) {N : Nat}
    (hN : ∀ j < N, ¬ L.RetAt g s (runX (L.mach M g) j s)) :
    ∀ j < N, ¬ L.RetAt g s₀ (runX (L.mach M g) j s₀) := fun j hj hr =>
  hN j hj ((h j fun k hk => hN k (by omega)).1.2 hr)

/-- **Twin runs (one level) compose.** -/
theorem TwinBaseC.trans {M : Nat} {g : Clif.Function} {s s₁ s₂ : Arm.ArmState}
    (h1 : L.TwinBaseC M g s s₁) (h2 : L.TwinBaseC M g s₁ s₂) : L.TwinBaseC M g s s₂ := by
  intro i hi
  have hi1 := L.noRetAt_twinC' h1 hi
  obtain ⟨r1, b1⟩ := h1 i hi
  obtain ⟨r2, b2⟩ := h2 i hi1
  refine ⟨r1.trans r2, fun hn => ?_⟩
  have hn1 : ¬ L.RetAt g s₁ (runX (L.mach M g) i s₁) := fun h => hn (r1.2 h)
  obtain ⟨p1, sp1, c1, m1⟩ := b1 hn
  obtain ⟨p2, sp2, c2, m2⟩ := b2 hn1
  refine ⟨p1.trans p2, sp1.trans sp2, fun h => (c1 h).trans (c2 h), fun h hc a ha => ?_⟩
  rw [m1 h hc a ha]
  exact m2 h ((c1 h).1 hc) a (sp1 ▸ ha)

/-- **Twin runs compose.** -/
theorem TwinC.trans : ∀ {M : Nat} {g : Clif.Function} {s s₁ s₂ : Arm.ArmState},
    L.TwinC M g s s₁ → L.TwinC M g s₁ s₂ → L.TwinC M g s s₂
  | 0, _, _, _, _, h1, h2 => TwinBaseC.trans L h1 h2
  | _ + 1, _, _, _, _, ⟨b1, n1⟩, ⟨b2, n2⟩ => ⟨TwinBaseC.trans L b1 b2, fun i hi h hc => by
      have hi1 := L.noRetAt_twinC' b1 hi
      have hn : ¬ L.RetAt _ _ _ := hi i (Nat.lt_succ_self i)
      have hct := ((b1 i fun j hj => hi j (by omega)).2 hn).2.2.1 h
      exact TwinC.trans (n1 i hi h hc) (n2 i hi1 h (hct.1 hc))⟩

end LinkSys

end E2E
