module

public import FV.E2E.LinkArmTwinC
public import FV.E2E.LinkArmBlrCheck

@[expose] public section

/-!
# Call-restricted twins from the machine lock (SEM1 #537, `docs/plans/uninit.md` §5.9,
determinism step)

The link-level half of `CallTwinC`/`DetRunPRBC`: what the per-index lock of two runs gives
(`backend_twoRunLERWZ`: `StEqOutX (R.Zc d d')`, whose sets avoid the callees' dead stack,
`RL.deadStack_eq_of_Zc`) turns into one level of `TwinC`/`TwinNC`, given

* the code image held by every state of both runs (`Ok.imgCode`'s premise, for
  `callsTo_iff_of_lock`),
* the body's `sp` `c` at the call states (for `slotByte_eq_of_lock`; the κ budget `K`),
* the return index `T`: neither run returns before `T`, both return at `T`.

**`twinBaseC_of_lock`**, **`twinNC_base_of_lock`** (the first clause of `TwinNC`),
`twinC_succ_of` (the nested clause, `TwinC (M + 1)` from one level and the callee twins).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)

/-- **The per-state clause of a twin from the lock** (pc, `sp`, program calls, the called
function's slot bytes). -/
theorem twinState_of_lock (hL : L.Ok) {g : Clif.Function} (hg : g ∈ L.P.funcs)
    (hc : (L.A g).fa.blrLow = true) {K : Nat} {c : BitVec 64} (hroom : K ≤ c.toNat)
    (hK : ∀ h, L.Callee g h → frameDrop (L.A h).af ≤ K) {Z : BitVec 64 → Prop}
    {u u' : Arm.ArmState} (hlk : StEqOutX Z u u') (hZ : ∀ a, StackBelow K c a → ¬ Z a)
    (himg : ∀ a, L.Img a → u.mem a = L.imgMem a) (himg' : ∀ a, L.Img a → u'.mem a = L.imgMem a)
    (hsp : ∀ h, L.CallsTo g u h → spv u = c) (hcal : ∀ h, L.CallsTo g u h → L.Callee g h) :
    Arm.r .PC u = Arm.r .PC u' ∧ spv u = spv u' ∧
      (∀ h, L.CallsTo g u h ↔ L.CallsTo g u' h) ∧
      ∀ h, L.CallsTo g u h → ∀ a, L.SlotByte h (spv u) a →
        u.mem (BitVec.ofNat 64 a) = u'.mem (BitVec.ofNat 64 a) := by
  refine ⟨hlk.1 .PC (by simp), hlk.1 _ (by simp), L.callsTo_iff_of_lock hL hg hc hlk himg himg',
    fun h hct a ha => ?_⟩
  rw [hsp h hct] at ha
  have hKh := hK h (hcal h hct)
  exact L.slotByte_eq_of_lock hL hg (hcal h hct) hKh (by omega)
    (fun b hb => hlk.2.2 b (hZ b hb)) ha

/-- **One level of call-restricted twins from the lock up to the shared return index `T`**
(module doc). -/
theorem twinBaseC_of_lock (hL : L.Ok) {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    (hc : (L.A g).fa.blrLow = true) {K : Nat} {c : BitVec 64} (hroom : K ≤ c.toNat)
    (hK : ∀ h, L.Callee g h → frameDrop (L.A h).af ≤ K) {s s₀ : Arm.ArmState} {T : Nat}
    (hlk : ∀ i < T, ∃ Z, StEqOutX Z (runX (L.mach M g) i s) (runX (L.mach M g) i s₀) ∧
      ∀ a, StackBelow K c a → ¬ Z a)
    (himg : ∀ i < T, ∀ a, L.Img a → (runX (L.mach M g) i s).mem a = L.imgMem a)
    (himg₀ : ∀ i < T, ∀ a, L.Img a → (runX (L.mach M g) i s₀).mem a = L.imgMem a)
    (hsp : ∀ i < T, ∀ h, L.CallsTo g (runX (L.mach M g) i s) h → spv (runX (L.mach M g) i s) = c)
    (hcal : ∀ i < T, ∀ h, L.CallsTo g (runX (L.mach M g) i s) h → L.Callee g h)
    (hnr : ∀ i < T, ¬ L.RetAt g s (runX (L.mach M g) i s) ∧
      ¬ L.RetAt g s₀ (runX (L.mach M g) i s₀))
    (hr : L.RetAt g s (runX (L.mach M g) T s) ∧ L.RetAt g s₀ (runX (L.mach M g) T s₀)) :
    L.TwinBaseC M g s s₀ := by
  intro i hi
  rcases Nat.lt_trichotomy i T with h | rfl | h
  · obtain ⟨n1, n2⟩ := hnr i h
    obtain ⟨Z, hz, hZ⟩ := hlk i h
    exact ⟨⟨fun e => absurd e n1, fun e => absurd e n2⟩, fun _ =>
      L.twinState_of_lock hL hg hc hroom hK hz hZ (himg i h) (himg₀ i h) (hsp i h) (hcal i h)⟩
  · exact ⟨⟨fun _ => hr.2, fun _ => hr.1⟩, fun hn => absurd hr.1 hn⟩
  · exact absurd hr.1 (hi T h)

/-- **The first clause of `TwinNC` from the lock up to `n`.** -/
theorem twinNC_base_of_lock (hL : L.Ok) {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    (hc : (L.A g).fa.blrLow = true) {K : Nat} {c : BitVec 64} (hroom : K ≤ c.toNat)
    (hK : ∀ h, L.Callee g h → frameDrop (L.A h).af ≤ K) {s s₀ : Arm.ArmState} {n : Nat}
    (hlk : ∀ i < n, ∃ Z, StEqOutX Z (runX (L.mach M g) i s) (runX (L.mach M g) i s₀) ∧
      ∀ a, StackBelow K c a → ¬ Z a)
    (himg : ∀ i < n, ∀ a, L.Img a → (runX (L.mach M g) i s).mem a = L.imgMem a)
    (himg₀ : ∀ i < n, ∀ a, L.Img a → (runX (L.mach M g) i s₀).mem a = L.imgMem a)
    (hsp : ∀ i < n, ∀ h, L.CallsTo g (runX (L.mach M g) i s) h → spv (runX (L.mach M g) i s) = c)
    (hcal : ∀ i < n, ∀ h, L.CallsTo g (runX (L.mach M g) i s) h → L.Callee g h) :
    ∀ i < n, Arm.r .PC (runX (L.mach M g) i s) = Arm.r .PC (runX (L.mach M g) i s₀) ∧
      spv (runX (L.mach M g) i s) = spv (runX (L.mach M g) i s₀) ∧
      (∀ h, L.CallsTo g (runX (L.mach M g) i s) h ↔ L.CallsTo g (runX (L.mach M g) i s₀) h) ∧
      ∀ h, L.CallsTo g (runX (L.mach M g) i s) h → ∀ a,
        L.SlotByte h (spv (runX (L.mach M g) i s)) a →
        (runX (L.mach M g) i s).mem (BitVec.ofNat 64 a) =
          (runX (L.mach M g) i s₀).mem (BitVec.ofNat 64 a) := fun i h =>
  let ⟨_, hz, hZ⟩ := hlk i h
  L.twinState_of_lock hL hg hc hroom hK hz hZ (himg i h) (himg₀ i h) (hsp i h) (hcal i h)

/-- **`TwinC (M + 1)` from one level and the callee twins at the calls.** -/
theorem twinC_succ_of {M : Nat} {g : Clif.Function} {s s₀ : Arm.ArmState}
    (hb : L.TwinBaseC (M + 1) g s s₀)
    (hn : ∀ i, (∀ j < i + 1, ¬ L.RetAt g s (runX (L.mach (M + 1) g) j s)) → ∀ h,
      L.CallsTo g (runX (L.mach (M + 1) g) i s) h →
      L.TwinC M h (enterAt (L.A h) (runX (L.mach (M + 1) g) i s))
        (enterAt (L.A h) (runX (L.mach (M + 1) g) i s₀))) :
    L.TwinC (M + 1) g s s₀ :=
  ⟨hb, hn⟩

end LinkSys

end E2E
