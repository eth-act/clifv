import FV.E2E.LinkArmProgCallPRBR

/-!
# `ThmPRBR` without program callees with slots (SEM1 #537, #680 (3), #687)

* `noRetAt_of`: at a machine entry whose return address is a linked call's (`RaOk (L.A g)
  (ra - 4)`), no state of the run before a step `n` without error (with `PostTrace` up to `n`) is
  a return (`RetAt`): past a return outside the code the machine errs (`retStuck`); a return
  after one of the code's calls has the body's `sp` (`PostTrace`), not the entry's. So the run's
  table (`TableOf`) covers the whole prefix up to the return.
* **`thmPRBR_of_thm`**: without program callees with slots (`¬ NeedSlots`), `Thm κ M` gives
  `ThmPRBR κ M` (the table prefix from `TableOf` by `noRetAt_of`; `NextAdv` is vacuous).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **No return before the return** (module doc). -/
theorem noRetAt_of (hL : L.Ok) {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (hME : L.MachEntry κ M g F G ra s w₀) (hra : RaOk (L.A g) (ra - 4)) {n : Nat}
    (htr : PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n)
    (herr : Arm.r .ERR (runX (L.mach M g) n s) = .None) :
    ∀ j < n, ¬ L.RetAt g s (runX (L.mach M g) j s) := by
  intro j hj hri
  have hc := hL.compiled g hg
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  have hx30 : xreg 30 s = ra := hME.abi.lr
  rcases hra with hra | ⟨hcp, hne⟩
  · have := retStuck (X := L.Xb) (H := L.hooks M) hc.layout hlm hri.2.2.1
      (by rw [hri.1, hx30]; intro k hk; have := hra k hk; rwa [BitVec.sub_add_cancel] at this)
      (n - j - 1)
    change Arm.r .ERR (runX (L.mach M g) (n - j - 1 + 1) (runX (L.mach M g) j s)) ≠ .None at this
    rw [← runX_add, show j + (n - j - 1 + 1) = n by omega] at this
    exact this herr
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · apply hne
      have h1 : Arm.r .PC s = xreg 30 s := hri.1
      rw [BitVec.sub_add_cancel, ← hx30, ← h1, hME.abi.pc]
    · have hsp := htr j hj0 hj ⟨_, hcp, by rw [hri.1, hx30, BitVec.sub_add_cancel]⟩
      rw [hri.2.2.2] at hsp
      have hfd := L.frameDrop_eq hL hg
      have hroom := hME.stack.1.1
      have e := congrArg BitVec.toNat hsp
      have hlt := (spv s).isLt
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at e
      omega

/-- **`ThmPRBR` from `Thm` without program callees with slots** (module doc). -/
theorem thmPRBR_of_thm (hL : L.Ok) (hN : ¬ L.NeedSlots) {M : Nat} (hT : L.Thm κ M) :
    L.ThmPRBR κ M := by
  intro g hg F vals cs w₀ fuel rvals cm' ini G ra s hWE hME hra htab hrun
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall, -⟩ :=
    hT g hg F vals cs w₀ fuel rvals cm' (hWE.toWorldEntry L hN) hrun
  obtain ⟨n, hret, htr⟩ := hall G ra s hME.entryP.entry
  obtain ⟨e, he⟩ := htab n (L.noRetAt_of hL hg hME.entryP.entry hra htr hret.ret.err)
  exact ⟨us, outs, wf, n, e, hus, hlen, hhold, hmem, hrs, hret, htr, he, fun h => absurd h hN⟩

end LinkSys

end E2E
