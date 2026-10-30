import FV.E2E.BackendTwoRunEitherK
import FV.E2E.BackendTwoRunVWitness

/-!
# Witnesses for the two-run lock inside `F ∪ D` (SEM1 #537, #713; `BackendTwoRunEitherK.lean`)

Non-vacuity of `backend_twoRunLERWZIUPF_eitherK` on both artifacts of the dispatch: its per-index
lock set lies inside the exterior `F` (here `D = ∅`), at every index before the return.

* `r_twoRunLERWZIUPF_eitherK_Lsl`: `LinkSlotSysWitness.Lsl`'s `r` (reads its uninitialised slot)
  with `Lsl`'s own compilation (legacy path, `CompiledEither.legacy`: `backend_twoRunLERWZIUPK`),
  run by the linked machine's hooks at any depth;
* `source_twoRunLERWZIUPF_eitherK`: `DeadCleanupWitness.source` through the cleanup path
  (`CompiledEither.cleanup`: `backend_twoRunLERWZIUPVK`).
-/

namespace E2E.TwoRunVWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup E2E.LinkSlotSysWitness
  E2E.LinkCheck
open E2E.LinkWitness (idHooks)

set_option maxHeartbeats 4000000 in
/-- **`backend_twoRunLERWZIUPF_eitherK` applies** to `Lsl`'s `r` with `Lsl`'s own (legacy)
compilation, run by the linked machine's hooks at any depth, for two entries: `RetAgreeX` at the
return and, at every index before it, the lock on a set inside `F`. -/
theorem r_twoRunLERWZIUPF_eitherK_Lsl (M : Nat) {F : BitVec 64 → Prop} {c : BitVec 64} {K : Nat}
    {args : List Clif.Val} {cs : Clif.State} {w₀ : Arm.ArmState} {env : Clif.Env}
    (hce : ClifEntry fR args cs)
    (hrel : RelW ⟨F, fun _ => none, (Lsl.A fR).af.slotBase,
      (RAFrame.compute (Lsl.A fR).vcp (Lsl.A fR).rf).intBase⟩ fR c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F fR.sig args w₀)
    (htr : TrapsExplicit env Lsl.P.bare cs) (fuel : Nat)
    {G G' : BitVec 64 → Prop} {base ra ra' : BitVec 64} {Kp Kp' : Nat} {cc cc' : BitVec 64}
    {Pp Pp' : Nat → BitVec 64 → BitVec 8} {Rr Rr' : Nat → Arm.ArmState} {s t0 : Arm.ArmState}
    (he : ActEntryPR (Lsl.A fR).vcp (Lsl.A fR).rf (Lsl.A fR).af (Lsl.A fR).fa (Lsl.A fR).fb K F G
      (ExtSemI.const Lsl.Xb) (Lsl.hooks M) base ra Kp cc Pp Rr s w₀)
    (he' : ActEntryPR (Lsl.A fR).vcp (Lsl.A fR).rf (Lsl.A fR).af (Lsl.A fR).fa (Lsl.A fR).fb K F G'
      (ExtSemI.const Lsl.Xb) (Lsl.hooks M) base ra' Kp' cc' Pp' Rr' t0 w₀)
    (hag : EntryAgree (frameDrop (Lsl.A fR).af + K) s t0)
    (hx29 : Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) t0) :
    ∀ vals cm, Clif.runLoop env Lsl.P.bare fuel cs = .returned vals cm →
      ∃ N, RetAgreeX (frameDrop (Lsl.A fR).af + K) (spv s)
        (iterN (ArmStepX Lsl.Xb (Lsl.hooks M) (Lsl.A fR).fa)
          ((prologueLines (Lsl.A fR).af.saves (Lsl.A fR).af.frameSize (Lsl.A fR).af.isCaller).length + N +
            ((epiLines (Lsl.A fR).af.saves (Lsl.A fR).af.frameSize).length + 1)) t0)
        (iterN (ArmStepX Lsl.Xb (Lsl.hooks M) (Lsl.A fR).fa)
          ((prologueLines (Lsl.A fR).af.saves (Lsl.A fR).af.frameSize (Lsl.A fR).af.isCaller).length + N +
            ((epiLines (Lsl.A fR).af.saves (Lsl.A fR).af.frameSize).length + 1)) s) ∧
        ∀ i < (prologueLines (Lsl.A fR).af.saves (Lsl.A fR).af.frameSize (Lsl.A fR).af.isCaller).length + N +
            ((epiLines (Lsl.A fR).af.saves (Lsl.A fR).af.frameSize).length + 1),
          ∃ Z : BitVec 64 → Prop, (∀ a, Z a → F a) ∧
            StEqOutX Z (iterN (ArmStepX Lsl.Xb (Lsl.hooks M) (Lsl.A fR).fa) i t0)
              (iterN (ArmStepX Lsl.Xb (Lsl.hooks M) (Lsl.A fR).fa) i s) := by
  have hc := fR_compiled
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  obtain ⟨body, psF, hpsF, -, hk⟩ := emitFunc_ok hc.emit
  have hx30 : (Lsl.A fR).fa.x30Free lm = true := by
    have h := fR_x30Free
    rwa [show getOk (labelOffsets (Lsl.A fR).fa.lines) = lm by rw [hlm]; rfl] at h
  have hnh := fR_noHookLines
  intro vals cm hrun
  obtain ⟨N, -, -, h, -, -, -, -, -, -, -, -, -, hlk⟩ := backend_twoRunLERWZIUPF_eitherK
    (D := fun _ => False)
    (XI := ExtSemI.const Lsl.Xb) (Lsl_ok.subset fR fR_mem) (.legacy hc) (instCallsOne_all fR)
    (tryCallsOne_all fR) (fun _ _ _ => fR_xcalls _ _ _) (fun _ _ _ => fR_xnif)
    (fun _ => lslTls F) (fun n b h => by cases h) rfl (fun _ h => h.elim) (fun _ => 0) hce hrel
    hrel hargs (SameWorld.refl _ _) (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl) htr fuel hrun hlm
    (hk ▸ hpsF) he (he'.toN 0)
    (fun n => (he'.calls n).mono fun _ hu => hu.1)
    (fun ht n => (he'.tries ht n).mono fun _ hu => hu.1)
    rfl (Lsl_ok.covered fR fR_mem) hx30
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, _, hj, _⟩ hd => (noHook_lineDest hnh hj hd).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨a, b, c, _, _, hj, _⟩ _ _ =>
      (noHook_line hnh hj).2.2 a b c rfl |>.elim)
    hag hx29
  refine ⟨N, h, fun i hi => ?_⟩
  obtain ⟨d, d', hz⟩ := hlk i hi
  exact ⟨_, fun a ha => ha.2.elim id False.elim, hz⟩

open DeadCleanupWitness in
set_option maxHeartbeats 4000000 in
/-- **`backend_twoRunLERWZIUPF_eitherK` applies** to the cleanup compilation of `source` through
the dispatch (`CompiledEither.cleanup`), for two entries: `RetAgreeX` at the return and, at every
index before it, the lock on a set inside `F`. -/
theorem source_twoRunLERWZIUPF_eitherK :
    ∃ vc vcp af fa fb, CompiledEither source 0 vc vcp (spillAlloc vcp) af fa fb ∧
      ∀ (env : Clif.Env) (K : Nat) (F : BitVec 64 → Prop) (c : BitVec 64) (w₀ : Arm.ArmState)
        (args : List Clif.Val) (cs : Clif.State),
        ClifEntry source args cs →
        RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
          source c cs.frame.slots cs.mem w₀ →
        ArgsAtEntry F source.sig args w₀ →
        TrapsExplicit env ({ funcs := [] } : Clif.Program) cs → ∀ fuel vals cm,
        Clif.runLoop env { funcs := [] } fuel cs = .returned vals cm →
        ∀ (G G' : BitVec 64 → Prop) (base ra ra' : BitVec 64) (Kp Kp' : Nat) (cc cc' : BitVec 64)
          (Pp Pp' : Nat → BitVec 64 → BitVec 8) (Rr Rr' : Nat → Arm.ArmState) (s t0 : Arm.ArmState),
          ActEntryPR vcp (spillAlloc vcp) af fa fb K F G (ExtSemI.const xQuiet) idHooks base ra Kp cc
            Pp Rr s w₀ →
          ActEntryPR vcp (spillAlloc vcp) af fa fb K F G' (ExtSemI.const xQuiet) idHooks base ra' Kp'
            cc' Pp' Rr' t0 w₀ →
          EntryAgree (frameDrop af + K) s t0 → Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) t0 →
          ∃ N, RetAgreeX (frameDrop af + K) (spv s)
            (iterN (ArmStepX xQuiet idHooks fa)
              ((prologueLines af.saves af.frameSize af.isCaller).length + N + ((epiLines af.saves af.frameSize).length + 1))
              t0)
            (iterN (ArmStepX xQuiet idHooks fa)
              ((prologueLines af.saves af.frameSize af.isCaller).length + N + ((epiLines af.saves af.frameSize).length + 1))
              s) ∧
            ∀ i < (prologueLines af.saves af.frameSize af.isCaller).length + N +
                ((epiLines af.saves af.frameSize).length + 1),
              ∃ Z : BitVec 64 → Prop, (∀ a, Z a → F a) ∧
                StEqOutX Z (iterN (ArmStepX xQuiet idHooks fa) i t0)
                  (iterN (ArmStepX xQuiet idHooks fa) i s) := by
  obtain ⟨vc, vcp, af, fa, fb, hc, hx30', hnh⟩ := cleanupChecks_sound source_cleanupChecks
  have hsub : InSubset ({ funcs := [] } : Clif.Program) source :=
    InSubset.of_verifiable input_conditions.1 (fun _ => rfl)
  refine ⟨vc, vcp, af, fa, fb, .cleanup hc, fun env K F c w₀ args cs hce hrel hargs htr fuel vals cm
    hrun G G' base ra ra' Kp Kp' cc cc' Pp Pp' Rr Rr' s t0 he he' hag hx29 => ?_⟩
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  obtain ⟨body, psF, hpsF, -, hk⟩ := emitFunc_ok hc.emit
  have hpsF' : blocksLinesE ⟨fa.k, af.slotBase⟩ af af.blocks.toList {} = .ok (body, psF) := by
    rw [hk]; exact hpsF
  have hx30 : fa.x30Free lm = true := by
    rwa [show getOk (labelOffsets fa.lines) = lm by rw [hlm]; rfl] at hx30'
  have hnil : (locsOf source.sig).zip args = [] := by
    rw [show locsOf source.sig = [] from rfl]; rfl
  obtain ⟨N, -, -, h, -, -, -, -, -, -, -, -, -, hlk⟩ := backend_twoRunLERWZIUPF_eitherK
    (D := fun _ => False) (XI := ExtSemI.const xQuiet) hsub (.cleanup hc) source_callsOne.1
    source_callsOne.2 (fun _ n _ => source_xcalls _ _ _ n)
    (fun _ _ _ => XNI.xnif (source_xni _ _ _ _ _)) (fun _ => xQuiet_tls F)
    (fun n b h => by cases h) rfl (fun _ h => h.elim) (fun _ => 0) hce hrel hrel hargs
    (SameWorld.refl _ _) (fun r v h => by simp [hnil] at h) (fun off v h => by simp [hnil] at h)
    htr fuel hrun hlm hpsF' he (he'.toN 0)
    (fun n => (he'.calls n).mono fun _ hu => hu.1)
    (fun ht n => (he'.tries ht n).mono fun _ hu => hu.1)
    rfl (formsCovered_cleanup_complete (lowerScope_of source_lowerScope) hc.lower hc.prepare _) hx30
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, _, hj, _⟩ hd => (noHook_lineDest hnh hj hd).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨a, b, c, _, _, hj, _⟩ _ _ =>
      (noHook_line hnh hj).2.2 a b c rfl |>.elim)
    hag hx29
  refine ⟨N, h, fun i hi => ?_⟩
  obtain ⟨d, d', hz⟩ := hlk i hi
  exact ⟨_, fun a ha => ha.2.elim id False.elim, hz⟩

end E2E.TwoRunVWitness
