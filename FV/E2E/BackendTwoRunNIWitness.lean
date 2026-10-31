import FV.E2E.BackendTwoRunNI
import FV.E2E.BackendTwoRunLRWitness

/-!
# Witness for the lock by induction on the call count (SEM1 #537, #713, `BackendTwoRunNI.lean`)

* `a2_twoRunLERWZI`: `backend_twoRunLERWZI` applies to `LinkWitness`'s compiled function `a2`
  (which calls externs) for two entries `s`, `t0` (any two agreeing as `EntryAgree` and on `x29`),
  along the paired run of the CLIF run (`backend_pairRunD`); the second entry's contracts at its
  locked call states come from its own `ActEntryPR` (`CalleeOkGP.mono`), the hook premises from
  `HookNIX` of the identity hooks.
-/

namespace E2E.LinkWitness

open Backend Backend.Proof Backend.Proof.Driver

/-- **`backend_twoRunLERWZI` applies** to `a2` with the identity hooks, for two entries. -/
theorem a2_twoRunLERWZI {F : BitVec 64 → Prop} {c : BitVec 64} {K : Nat} {args : List Clif.Val}
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
      ∃ N, RetAgreeX (frameDrop (A fA2).af + K) (spv s)
        (iterN (ArmStepX Xb idHooks (A fA2).fa)
          ((prologueLines (A fA2).af.saves (A fA2).af.frameSize (A fA2).af.isCaller).length + N +
            ((epiLines (A fA2).af.saves (A fA2).af.frameSize).length + 1)) t0)
        (iterN (ArmStepX Xb idHooks (A fA2).fa)
          ((prologueLines (A fA2).af.saves (A fA2).af.frameSize (A fA2).af.isCaller).length + N +
            ((epiLines (A fA2).af.saves (A fA2).af.frameSize).length + 1)) s) := by
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
  obtain ⟨N, -, -, h, -, -⟩ := backend_twoRunLERWZI hc (fun _ => 0) (SameWorld.refl _ _) hs hvb hkk
    hops hvals hsem hlm (hk ▸ hpsF) he (he'.toN 0)
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
  exact ⟨N, h⟩

end E2E.LinkWitness
