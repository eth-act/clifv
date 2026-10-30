import FV.E2E.LinkArmTwinCLock
import FV.E2E.BackendTwoRunL

/-!
# The two-run lock at the link, as call-restricted twins (SEM1 #537, #713)

`backend_twoRunLERWZI`'s per-index lock is stated for the activation's machine
`({ R with X := XI.at 0 }).step` (`R = actRL …`). At the link the activation of `g` runs on
`L.mach M g = ArmStepX L.Xb (L.hooks M) (L.A g).fa`; the two agree when `XI`'s symbols are the
base's (`ArmStepX` reads `X` only through `sym`). The lock sets `R.Zc d d'` avoid the callees' dead
stack (`StackBelow R.K R.spB`), which is what `twinNC_base_of_lock` needs:

* `actRL_step_mach`, `actRL_step_mach'` (the two entries' machines are `L.mach M g`);
* **`twinNC_base_of_twoRun`**: the first clause of `TwinNC` from the lock in the backend's form.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)

/-- **The activation's machine at the link is `L.mach M g`** (`XI`'s symbols the base's). -/
theorem actRL_step_mach {M : Nat} {g : Clif.Function} {lm : Std.HashMap Lbl Nat}
    {base : BitVec 64} {s : Arm.ArmState} {XI : ExtSemI} {psF : PState} {K : Nat}
    {G : BitVec 64 → Prop} {gv : Nat → String → Prop} (hs : XI.sym = L.Xb.sym) :
    ({ Backend.Proof.actRL (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb lm base s XI (L.hooks M) psF
      K G gv with X := XI.at 0 } : RL).step = L.mach M g :=
  armStepX_congr_sym (X := XI.at 0) hs _ _

/-- **The second entry's machine at the link is `L.mach M g`.** -/
theorem actRL_step_mach' {M : Nat} {g : Clif.Function} {lm : Std.HashMap Lbl Nat}
    {base : BitVec 64} {s t0 : Arm.ArmState} {XI : ExtSemI} {psF : PState} {K : Nat}
    {G G' : BitVec 64 → Prop} {gv : Nat → String → Prop} (hs : XI.sym = L.Xb.sym) :
    ({ Backend.Proof.actRL (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb lm base s XI (L.hooks M) psF
      K G gv with s0 := t0, G := G', X := XI.at 0 } : RL).step = L.mach M g :=
  armStepX_congr_sym (X := XI.at 0) hs _ _

/-- **The first clause of `TwinNC` from the backend's per-index lock** (module doc): the lock with
the sets `R.Zc d d'` up to `n` between the second entry `t0` and the first `s`, with the code image
held by both runs, the body's `sp` at the first run's program calls and the callees in `Callee`. -/
theorem twinNC_base_of_twoRun (hL : L.Ok) {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    (hc : (L.A g).fa.blrLow = true) {lm : Std.HashMap Lbl Nat} {base : BitVec 64}
    {s t0 : Arm.ArmState} {XI : ExtSemI} (hs : XI.sym = L.Xb.sym) {psF : PState} {K : Nat}
    {G G' : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hroom : K ≤ (spv s - BitVec.ofNat 64 (frameDrop (L.A g).af)).toNat)
    (hK : ∀ h, L.Callee g h → frameDrop (L.A h).af ≤ K) {n : Nat}
    (hlk : ∀ i < n, ∃ d d', StEqOutX
      ((Backend.Proof.actRL (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb lm base s XI (L.hooks M) psF
        K G gv).Zc d d')
      (iterN ({ Backend.Proof.actRL (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb lm base s XI
        (L.hooks M) psF K G gv with s0 := t0, G := G', X := XI.at 0 } : RL).step i t0)
      (iterN ({ Backend.Proof.actRL (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb lm base s XI
        (L.hooks M) psF K G gv with X := XI.at 0 } : RL).step i s))
    (himg : ∀ i < n, ∀ a, L.Img a → (runX (L.mach M g) i t0).mem a = L.imgMem a)
    (himg₀ : ∀ i < n, ∀ a, L.Img a → (runX (L.mach M g) i s).mem a = L.imgMem a)
    (hsp : ∀ i < n, ∀ h, L.CallsTo g (runX (L.mach M g) i t0) h →
      spv (runX (L.mach M g) i t0) = spv s - BitVec.ofNat 64 (frameDrop (L.A g).af))
    (hcal : ∀ i < n, ∀ h, L.CallsTo g (runX (L.mach M g) i t0) h → L.Callee g h) :
    ∀ i < n, Arm.r .PC (runX (L.mach M g) i t0) = Arm.r .PC (runX (L.mach M g) i s) ∧
      spv (runX (L.mach M g) i t0) = spv (runX (L.mach M g) i s) ∧
      (∀ h, L.CallsTo g (runX (L.mach M g) i t0) h ↔ L.CallsTo g (runX (L.mach M g) i s) h) ∧
      ∀ h, L.CallsTo g (runX (L.mach M g) i t0) h → ∀ a,
        L.SlotByte h (spv (runX (L.mach M g) i t0)) a →
        (runX (L.mach M g) i t0).mem (BitVec.ofNat 64 a) =
          (runX (L.mach M g) i s).mem (BitVec.ofNat 64 a) := by
  refine L.twinNC_base_of_lock hL hg hc hroom hK (fun i hi => ?_) himg himg₀ hsp hcal
  obtain ⟨d, d', hz⟩ := hlk i hi
  rw [L.actRL_step_mach hs, L.actRL_step_mach' hs, ← runX_eq, ← runX_eq] at hz
  exact ⟨_, hz, fun a ha hzz => hzz.2.2.1 ha⟩

end LinkSys

end E2E
