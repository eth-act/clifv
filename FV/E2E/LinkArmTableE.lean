import FV.E2E.LinkArmTableB

/-!
# The prefix-closed machine table (SEM1 #537, #680 (3), fix of #700, step 1)

`TableOf M g s ini` (`LinkArmTableB.lean`) asks, at every call of every prefix before the
return, that the callee's run returns (`TabUpTo`'s `∃ N', RetOf …`), so it is false for every
`ini` when a callee never returns ([#700](https://github.com/eth-act/clifv/issues/700)), and a
top-level entry cannot discharge it. The prefix-closed variant asks nothing about returns:

* `TabUpToE M g s b k N e`: as `TabUpTo`, but at each call of the prefix the callee's table is
  given for **every** prefix of the callee's run before its first return without an error
  (`∃ e'`), and, only when the callee returns, the call's count `E j` is pinned by the
  callee run's full `TabUpTo` up to its return (`slotted h` plus its count; a returning callee's
  nested calls all returned, so `tabUpTo_count` applies); at depth `0` only `e = 0`;
* `TableOfE M g s ini`: every prefix before the return **whose states have no error** has a
  `TabUpToE` with `ini`'s table.

Here: `tabUpToE_zero`, `tabUpToE_mono`, **`tabUpToE_of`** (`TabUpTo → TabUpToE`),
**`tableOfE_of`** (`TableOf → TableOfE`: `TableOfE` is the weaker premise),
`tableOfE_of_retAt`, `tableOfE_of_err` (a run with an error at its entry has the table of every
oracle; with `TableOf` that needs `RetAt` at the entry).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)

/-- **The prefix-closed machine-side table of a run prefix** (module doc). -/
def TabUpToE : Nat → Clif.Function → Arm.ArmState → (Nat → Nat → BitVec 8) → Nat → Nat → Nat →
    Prop
  | 0, _, _, _, _, _, e => e = 0
  | M + 1, g, s, b, k, N, e => ∃ E : Nat → Nat,
      e = Clif.sumTo E (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s N) ∧
      ∀ i < N, CallPc (L.A g).fa (L.A g).base (Arm.r .PC (runX (L.mach (M + 1) g) i s)) →
        ((∀ h, ¬ L.CallsTo g (runX (L.mach (M + 1) g) i s) h) →
          E (callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i) = 0) ∧
        ∀ h, L.CallsTo g (runX (L.mach (M + 1) g) i s) h →
          let t := runX (L.mach (M + 1) g) i s
          let j := callsBefore (L.mach (M + 1) g) (L.A g).fa (L.A g).base s i
          (slotted h = 1 → ∀ a, L.SlotByte h (spv t) a →
            b (k + Clif.sumTo E j + 1) a = probeMem (L.A h).af t (BitVec.ofNat 64 a)) ∧
          slotted h ≤ E j ∧
          (∀ N', (∀ N'' < N', ¬ RetOf (L.A h) t (runX (L.mach M h) N'' (enterAt (L.A h) t))) →
            (∀ N'' < N', Arm.r .ERR (runX (L.mach M h) N'' (enterAt (L.A h) t)) = .None) →
            ∃ e', TabUpToE M h (enterAt (L.A h) t) b (k + Clif.sumTo E j + slotted h) N' e') ∧
          ∀ N', RetOf (L.A h) t (runX (L.mach M h) N' (enterAt (L.A h) t)) →
            (∀ N'' < N', ¬ RetOf (L.A h) t (runX (L.mach M h) N'' (enterAt (L.A h) t))) →
            TabUpTo L M h (enterAt (L.A h) t) b (k + Clif.sumTo E j + slotted h) N'
              (E j - slotted h)

/-- **The run's prefix-closed table is `ini`'s**: every prefix before the return whose states
have no error has a `TabUpToE` with `ini`'s table. -/
def TableOfE (M : Nat) (g : Clif.Function) (s : Arm.ArmState) (ini : Clif.SlotInit) : Prop :=
  ∀ N, (∀ j < N, ¬ L.RetAt g s (runX (L.mach M g) j s)) →
    (∀ j < N, Arm.r .ERR (runX (L.mach M g) j s) = .None) →
    ∃ e, L.TabUpToE M g s ini.bytes ini.next N e

/-- The empty prefix has the prefix-closed table of count `0`. -/
theorem tabUpToE_zero (M : Nat) (g : Clif.Function) (s : Arm.ArmState) (b : Nat → Nat → BitVec 8)
    (k : Nat) : L.TabUpToE M g s b k 0 0 := by
  cases M with
  | zero => rfl
  | succ M => exact ⟨fun _ => 0, by simp [callsBefore, Clif.sumTo],
      fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- **A shorter prefix has a prefix-closed table** (the same per-call counts). -/
theorem tabUpToE_mono {M : Nat} {g : Clif.Function} {s : Arm.ArmState} {b : Nat → Nat → BitVec 8}
    {k N e : Nat} (h : L.TabUpToE M g s b k N e) {N' : Nat} (hN : N' ≤ N) :
    ∃ e', L.TabUpToE M g s b k N' e' := by
  cases M with
  | zero => exact ⟨0, rfl⟩
  | succ M =>
    obtain ⟨E, -, hE⟩ := h
    exact ⟨_, E, rfl, fun i hi => hE i (by omega)⟩

/-- Two first returns of a callee run are the same step. -/
theorem firstRet_unique {a : Art} {Mm : Arm.ArmState → Arm.ArmState} {t u : Arm.ArmState}
    {N₁ N₂ : Nat} (h₁ : RetOf a t (runX Mm N₁ u)) (hm₁ : ∀ N'' < N₁, ¬ RetOf a t (runX Mm N'' u))
    (h₂ : RetOf a t (runX Mm N₂ u)) (hm₂ : ∀ N'' < N₂, ¬ RetOf a t (runX Mm N'' u)) : N₁ = N₂ := by
  rcases Nat.lt_trichotomy N₁ N₂ with e | e | e
  · exact absurd h₁ (hm₂ _ e)
  · exact e
  · exact absurd h₂ (hm₁ _ e)

/-- **A table is a prefix-closed table** (`TabUpTo → TabUpToE`). -/
theorem tabUpToE_of : ∀ (M : Nat) (g : Clif.Function) (s : Arm.ArmState)
    (b : Nat → Nat → BitVec 8) (k N e : Nat), L.TabUpTo M g s b k N e → L.TabUpToE M g s b k N e
  | 0, _, _, _, _, _, _, h => h.1
  | M + 1, g, s, b, k, N, e, h => by
    obtain ⟨E, he, hE⟩ := h
    refine ⟨E, he, fun i hi hpc => ⟨(hE i hi hpc).1, fun h hch => ?_⟩⟩
    obtain ⟨hsb, hle, N₁, hr₁, hm₁, ht₁⟩ := (hE i hi hpc).2 h hch
    refine ⟨hsb, hle, fun N' hN' _ => ?_, fun N' hr hm => ?_⟩
    · have hle' : N' ≤ N₁ := by
        rcases Nat.lt_or_ge N₁ N' with hlt | hge
        · exact absurd hr₁ (hN' N₁ hlt)
        · exact hge
      obtain ⟨e', he'⟩ := L.tabUpTo_mono ht₁ hle'
      exact ⟨e', tabUpToE_of M h _ b _ N' e' he'⟩
    · obtain rfl := firstRet_unique hr hm hr₁ hm₁
      exact ht₁

/-- **`TableOf` gives `TableOfE`**: the prefix-closed premise is the weaker one. -/
theorem tableOfE_of {M : Nat} {g : Clif.Function} {s : Arm.ArmState} {ini : Clif.SlotInit}
    (h : L.TableOf M g s ini) : L.TableOfE M g s ini := fun N hN _ => by
  obtain ⟨e, he⟩ := h N hN
  exact ⟨e, L.tabUpToE_of M g s ini.bytes ini.next N e he⟩

/-- A run that has returned at its entry has the prefix-closed table of every oracle. -/
theorem tableOfE_of_retAt {M : Nat} {g : Clif.Function} {s : Arm.ArmState}
    (h : L.RetAt g s s) (ini : Clif.SlotInit) : L.TableOfE M g s ini :=
  L.tableOfE_of (L.tableOf_of_retAt h ini)

/-- **A run with an error at its entry has the prefix-closed table of every oracle** (only the
empty prefix is error-free). -/
theorem tableOfE_of_err {M : Nat} {g : Clif.Function} {s : Arm.ArmState}
    (h : Arm.r .ERR s ≠ .None) (ini : Clif.SlotInit) : L.TableOfE M g s ini := by
  intro N _ hE
  cases N with
  | zero => exact ⟨0, L.tabUpToE_zero M g s ini.bytes ini.next⟩
  | succ N => exact absurd (hE 0 (Nat.succ_pos N)) h

end LinkSys

end E2E
