import FV.E2E.BackendTwoRunNIU
import FV.E2E.BackendTwoRunLRWitness

/-!
# Witnesses for the call-state world agreement and the lock up to the call state (SEM1 #537,
#713, `BackendTwoRunNZW.lean`, `BackendTwoRunNIU.lean`)

* `lockedUpTo_self`: every run is locked up to every index with itself (`LockedUpTo` is
  satisfiable for any machine);
* `lockedUpTo_x30`: a state differing from the first run's only in `x30` at index `0` is locked
  up to index `0` (distinct states);
* `a2_twoRunLERWZNpW`: `backend_twoRunLERWZNpW` applies to `LinkWitness`'s compiled function `a2`
  (which calls externs) for two entries and any prefix bound `N`, along the paired run of the CLIF
  run (`backend_pairRunD`), hook premises from `HookNIX` of the identity hooks;
* `a2_twoRunLERWZIU`: `backend_twoRunLERWZIU` on `a2`, the second entry's contracts at its locked
  call states from its own `ActEntryPR` (`CalleeOkGP.mono`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **Every run is locked with itself up to every index.** -/
theorem lockedUpTo_self (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm) (base : BitVec 64)
    (K : Nat) (c : BitVec 64) (F D : BitVec 64 → Prop) (s : Arm.ArmState) (i : Nat) :
    LockedUpTo Mm fa base K c F D s s (callsBefore Mm fa base s i) (runX Mm i s) :=
  ⟨i, rfl, rfl, fun j _ => ⟨fun _ => False, StEqOutX.refl _ _, fun _ _ h => h⟩,
    fun _ _ _ => rfl⟩

/-- **A state differing in `x30` is locked at index `0`** (two distinct states). -/
theorem lockedUpTo_x30 (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm) (base : BitVec 64)
    (K : Nat) (c : BitVec 64) (F D : BitVec 64 → Prop) (s : Arm.ArmState) (v : BitVec 64) :
    LockedUpTo Mm fa base K c F D s (Arm.w (.GPR 30#5) v s) 0 (Arm.w (.GPR 30#5) v s) := by
  refine ⟨0, rfl, rfl, fun j hj => ⟨fun _ => False, ?_, fun _ _ h => h⟩, fun _ _ _ => ?_⟩
  · obtain rfl : j = 0 := Nat.le_zero.mp hj
    refine ⟨fun f hf => ?_, ?_, fun _ _ => ?_⟩
    · show Arm.r f (Arm.w (.GPR 30#5) v s) = Arm.r f s
      rw [Arm.r_of_w_different hf]
    · show (Arm.w (.GPR 30#5) v s).program = s.program
      simp [Arm.w_program]
    · show (Arm.w (.GPR 30#5) v s).mem _ = s.mem _
      simp [Arm.w, Arm.write_base_gpr]
  · show (Arm.w (.GPR 30#5) v s).mem _ = s.mem _
    simp [Arm.w, Arm.write_base_gpr]

end E2E

namespace E2E.LinkWitness

open Backend Backend.Proof Backend.Proof.Driver

/-- **`backend_twoRunLERWZNpW` applies** to `a2` with the identity hooks, for two entries and any
prefix bound `N`. -/
theorem a2_twoRunLERWZNpW {F : BitVec 64 → Prop} {c : BitVec 64} {K : Nat} {args : List Clif.Val}
    {cs : Clif.State} {w₀ : Arm.ArmState} (hce : ClifEntry fA2 args cs)
    (hrel : RelW ⟨F, fun _ => none, (A fA2).af.slotBase,
      (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase⟩ fA2 c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F fA2.sig args w₀)
    (htr : TrapsExplicit Clif.Rust.env (L F).P.bare cs) (fuel : Nat)
    {G G' : BitVec 64 → Prop} {base ra ra' : BitVec 64} {Kp Kp' : Nat} {cc cc' : BitVec 64}
    {Pp Pp' : Nat → BitVec 64 → BitVec 8} {Rr Rr' : Nat → Arm.ArmState} {s t0 : Arm.ArmState}
    (he : ActEntryPR (A fA2).vcp (A fA2).rf (A fA2).af (A fA2).fa (A fA2).fb K F G
      (ExtSemI.const Xb) idHooks base ra Kp cc Pp Rr s w₀)
    (he' : ActEntryPR (A fA2).vcp (A fA2).rf (A fA2).af (A fA2).fa (A fA2).fb K F G'
      (ExtSemI.const Xb) idHooks base ra' Kp' cc' Pp' Rr' t0 w₀)
    (hag : EntryAgree (frameDrop (A fA2).af + K) s t0)
    (hx29 : Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) t0) (N : Nat) :
    ∀ vals cm, Clif.runLoop Clif.Rust.env (L F).P.bare fuel cs = .returned vals cm →
      ∃ C, (C ≤ N → ∃ T, RetAgreeX (frameDrop (A fA2).af + K) (spv s)
        (iterN (ArmStepX Xb idHooks (A fA2).fa)
          ((prologueLines (A fA2).af.saves (A fA2).af.frameSize (A fA2).af.isCaller).length + T +
            ((epiLines (A fA2).af.saves (A fA2).af.frameSize).length + 1)) t0)
        (iterN (ArmStepX Xb idHooks (A fA2).fa)
          ((prologueLines (A fA2).af.saves (A fA2).af.frameSize (A fA2).af.isCaller).length + T +
            ((epiLines (A fA2).af.saves (A fA2).af.frameSize).length + 1)) s)) ∧
      (N < C → ∃ T, ∀ a, ¬ F a → ¬ False →
        (iterN (ArmStepX Xb idHooks (A fA2).fa)
          ((prologueLines (A fA2).af.saves (A fA2).af.frameSize (A fA2).af.isCaller).length + T) t0).mem a =
        (iterN (ArmStepX Xb idHooks (A fA2).fa)
          ((prologueLines (A fA2).af.saves (A fA2).af.frameSize (A fA2).af.isCaller).length + T) s).mem a) := by
  have hL := L_ok (fun _ => True) (fun _ _ => trivial)
  have hA2 : fA2 ∈ P.funcs := by simp [P]
  have hc := a2_compiled
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  obtain ⟨body, psF, hpsF, -, hk⟩ := emitFunc_ok hc.emit
  have hx30 : (A fA2).fa.x30Free lm = true := by
    have h := List.all_eq_true.mp x30Free_all fA2 hA2
    rwa [show getOk (labelOffsets (A fA2).fa.lines) = lm by rw [hlm]; rfl] at h
  intro vals cm hrun
  obtain ⟨us, outs, w, ⟨b, kk, ρ, w₁, vb, ops, outs', hs, hvb, hkk, hops, hvals, hsem⟩, -⟩ :=
    backend_pairRunD (D := fun _ => False) (XI := ExtSemI.const Xb) (hL.subset fA2 hA2) hc
      a2_callsOne.1 a2_callsOne.2 (fun _ n _ => a2_xcalls _ _ _ n) (fun _ _ _ => xb_xNI)
      (fun _ => xbTls F) (fun n b h => by cases h) rfl (fun _ => 0) hce hrel hrel hargs
      (SameWorld.refl _ _) (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl) htr fuel vals cm hrun
  have key := backend_twoRunLERWZNpW (N := N) hc (fun _ => 0) (SameWorld.refl _ _) hs hvb hkk
    hops hvals hsem hlm (hk ▸ hpsF) (he.toN N) (he'.toN N)
    rfl (hL.covered fA2 hA2) hx30
    (fun _ _ _ _ _ _ _ _ _ _ _ hl hW _ _ _ _ =>
      stEqOutX_call_of_hookNIX_D (BD := fun _ => True) (hookNIX_id _ _)
        (fun a h => by
          show frameWG K (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase
            (RAFrame.compute (A fA2).vcp (A fA2).rf).size (A fA2).af G s a
          rw [he.hF]; exact h.resolve_right id) hW
        trivial hl)
    (fun _ _ _ _ _ _ _ _ _ _ _ hl hW _ m r =>
      stEqOutX_tls_of_hookNIX_D (BD := fun _ => True) (hookNIX_id _ _)
        (fun a h => by
          show frameWG K (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase
            (RAFrame.compute (A fA2).vcp (A fA2).rf).size (A fA2).af G s a
          rw [he.hF]; exact h.resolve_right id) hW
        m r hl)
    hag hx29
  refine ⟨w₁.2, fun hle => ?_, fun hlt => ?_⟩
  · obtain ⟨T, -, -, h, -, -⟩ := key.1 hle
    exact ⟨T, h⟩
  · obtain ⟨T, -, -, -, -, -, h⟩ := key.2 hlt
    exact ⟨T, h⟩

/-- **`backend_twoRunLERWZIU` applies** to `a2` with the identity hooks, for two entries; the
second entry's contracts at its locked call states from its own `ActEntryPR`. -/
theorem a2_twoRunLERWZIU {F : BitVec 64 → Prop} {c : BitVec 64} {K : Nat} {args : List Clif.Val}
    {cs : Clif.State} {w₀ : Arm.ArmState} (hce : ClifEntry fA2 args cs)
    (hrel : RelW ⟨F, fun _ => none, (A fA2).af.slotBase,
      (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase⟩ fA2 c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F fA2.sig args w₀)
    (htr : TrapsExplicit Clif.Rust.env (L F).P.bare cs) (fuel : Nat)
    {G G' : BitVec 64 → Prop} {base ra ra' : BitVec 64} {Kp Kp' : Nat} {cc cc' : BitVec 64}
    {Pp Pp' : Nat → BitVec 64 → BitVec 8} {Rr Rr' : Nat → Arm.ArmState} {s t0 : Arm.ArmState}
    (he : ActEntryPR (A fA2).vcp (A fA2).rf (A fA2).af (A fA2).fa (A fA2).fb K F G
      (ExtSemI.const Xb) idHooks base ra Kp cc Pp Rr s w₀)
    (he' : ActEntryPR (A fA2).vcp (A fA2).rf (A fA2).af (A fA2).fa (A fA2).fb K F G'
      (ExtSemI.const Xb) idHooks base ra' Kp' cc' Pp' Rr' t0 w₀)
    (hag : EntryAgree (frameDrop (A fA2).af + K) s t0)
    (hx29 : Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) t0) :
    ∀ vals cm, Clif.runLoop Clif.Rust.env (L F).P.bare fuel cs = .returned vals cm →
      ∃ T, RetAgreeX (frameDrop (A fA2).af + K) (spv s)
        (iterN (ArmStepX Xb idHooks (A fA2).fa)
          ((prologueLines (A fA2).af.saves (A fA2).af.frameSize (A fA2).af.isCaller).length + T +
            ((epiLines (A fA2).af.saves (A fA2).af.frameSize).length + 1)) t0)
        (iterN (ArmStepX Xb idHooks (A fA2).fa)
          ((prologueLines (A fA2).af.saves (A fA2).af.frameSize (A fA2).af.isCaller).length + T +
            ((epiLines (A fA2).af.saves (A fA2).af.frameSize).length + 1)) s) ∧
      ∀ a, ¬ F a →
        (iterN (ArmStepX Xb idHooks (A fA2).fa)
          ((prologueLines (A fA2).af.saves (A fA2).af.frameSize (A fA2).af.isCaller).length + T +
            ((epiLines (A fA2).af.saves (A fA2).af.frameSize).length + 1)) t0).mem a =
        (iterN (ArmStepX Xb idHooks (A fA2).fa)
          ((prologueLines (A fA2).af.saves (A fA2).af.frameSize (A fA2).af.isCaller).length + T +
            ((epiLines (A fA2).af.saves (A fA2).af.frameSize).length + 1)) s).mem a := by
  have hL := L_ok (fun _ => True) (fun _ _ => trivial)
  have hA2 : fA2 ∈ P.funcs := by simp [P]
  have hc := a2_compiled
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  obtain ⟨body, psF, hpsF, -, hk⟩ := emitFunc_ok hc.emit
  have hx30 : (A fA2).fa.x30Free lm = true := by
    have h := List.all_eq_true.mp x30Free_all fA2 hA2
    rwa [show getOk (labelOffsets (A fA2).fa.lines) = lm by rw [hlm]; rfl] at h
  intro vals cm hrun
  obtain ⟨us, outs, w, ⟨b, kk, ρ, w₁, vb, ops, outs', hs, hvb, hkk, hops, hvals, hsem⟩, -⟩ :=
    backend_pairRunD (D := fun _ => False) (XI := ExtSemI.const Xb) (hL.subset fA2 hA2) hc
      a2_callsOne.1 a2_callsOne.2 (fun _ n _ => a2_xcalls _ _ _ n) (fun _ _ _ => xb_xNI)
      (fun _ => xbTls F) (fun n b h => by cases h) rfl (fun _ => 0) hce hrel hrel hargs
      (SameWorld.refl _ _) (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl) htr fuel vals cm hrun
  obtain ⟨T, -, -, h, hm, -⟩ := backend_twoRunLERWZIU hc (fun _ => 0) (SameWorld.refl _ _) hs hvb
    hkk hops hvals hsem hlm (hk ▸ hpsF) he (he'.toN 0)
    (fun n => (he'.calls n).mono fun _ hu => hu.1)
    (fun ht n => (he'.tries ht n).mono fun _ hu => hu.1)
    rfl (hL.covered fA2 hA2) hx30
    (fun _ _ _ _ _ _ _ _ _ _ _ _ hl hW _ _ _ _ =>
      stEqOutX_call_of_hookNIX_D (BD := fun _ => True) (hookNIX_id _ _)
        (fun a h => by
          show frameWG K (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase
            (RAFrame.compute (A fA2).vcp (A fA2).rf).size (A fA2).af G s a
          rw [he.hF]; exact h.resolve_right id) hW
        trivial hl)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ hl hW _ m r =>
      stEqOutX_tls_of_hookNIX_D (BD := fun _ => True) (hookNIX_id _ _)
        (fun a h => by
          show frameWG K (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase
            (RAFrame.compute (A fA2).vcp (A fA2).rf).size (A fA2).af G s a
          rw [he.hF]; exact h.resolve_right id) hW
        m r hl)
    hag hx29
  exact ⟨T, h, fun a ha => hm a ha id⟩

end E2E.LinkWitness
