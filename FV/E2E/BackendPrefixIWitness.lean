import FV.E2E.DeadCleanupPrefix
import FV.E2E.IselSimIWitness
import FV.E2E.BackendWorldCleanupIWitness

/-!
# Witnesses for the counted pipeline up to call `N` (`FV/E2E/BackendPrefixI.lean`,
`FV/E2E/DeadCleanupPrefix.lean`)

`backend_prefixPRI` applies to `LinkWitness`'s compiled function `a2`, `backend_prefix_cleanupPRI`
to the closed cleanup compilation of `DeadCleanupWitness.source` (the entry premises and the
machine entry remain); `ExtSemI.upTo` keeps the calls below `N`.
-/

namespace E2E.LinkWitness

open Backend Backend.Proof Backend.Proof.Driver

theorem upTo_const_at (X : ExtSem) : ((ExtSemI.const X).upTo 2).at 1 = X :=
  ((ExtSemI.const X).upTo_at_lt (by decide)).trans (ExtSemI.const_at X 1)

theorem a2_prefixPRI {F : BitVec 64 → Prop} {c : BitVec 64} {K : Nat} {args : List Clif.Val}
    {cs : Clif.State} {w₀ : Arm.ArmState} (hce : ClifEntry fA2 args cs)
    (hrel : RelW ⟨F, fun _ => none, (A fA2).af.slotBase,
      (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase⟩ fA2 c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F fA2.sig args w₀)
    (htr : TrapsExplicit Clif.Rust.env (L F).P.bare cs) {N : Nat} {H : ArmHooks}
    {G : BitVec 64 → Prop} {base ra : BitVec 64} {Kp : Nat} {cc : BitVec 64}
    {Pp : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {s : Arm.ArmState}
    (he : ActEntryPRN (A fA2).vcp (A fA2).rf (A fA2).af (A fA2).fa (A fA2).fb K F G
      (ExtSemI.const Xb) H base ra Kp cc Pp R s w₀ N)
    {t : Clif.State} (hr : ReachN Clif.Rust.env (L F).P.bare cs t N) (hcn : callNum t = 1) :
    ∀ j < N, ∃ u i info uses w r, OnCall (ArmStepX ((ExtSemI.const Xb).at 0) H (A fA2).fa)
        (A fA2).fa base s j u ∧
      spOf u = spv s - BitVec.ofNat 64 (frameDrop (A fA2).af) ∧
      CallSiteAt F K G s (A fA2).fa base i uses w u ∧
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) ∧
      ((ExtSemI.const Xb).at j).call (callDest info) uses w = some r := by
  have hL := L_ok (fun _ => True) (fun _ _ => trivial)
  have hA2 : fA2 ∈ P.funcs := by simp [P]
  exact backend_prefixPRI (hL.subset fA2 hA2) a2_compiled a2_callsOne.1 a2_callsOne.2
    (hL.covered fA2 hA2) (fun _ n _ => a2_xcalls _ _ _ n) (fun n b h => by cases h) rfl hce hrel
    hargs htr he hr hcn

end E2E.LinkWitness

namespace E2E.DeadCleanupWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **`backend_prefix_cleanupPRI` applies** to the closed cleanup compilation of `source`. -/
theorem prefix_cleanupPRI_applies :
    ∃ vc vcp af fa fb, CompiledCleanup source 0 vc vcp (spillAlloc vcp) af fa fb ∧
      ∀ (env : Clif.Env) (XI : ExtSemI) (K : Nat) (F : BitVec 64 → Prop) (c : BitVec 64)
        (w₀ : Arm.ArmState) (args : List Clif.Val) (cs : Clif.State),
        ClifEntry source args cs →
        RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
          source c cs.frame.slots cs.mem w₀ →
        ArgsAtEntry F source.sig args w₀ →
        TrapsExplicit env ({ funcs := [] } : Clif.Program) cs →
        ∀ (N : Nat) (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat)
          (cc : BitVec 64) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
          (s : Arm.ArmState),
          ActEntryPRN vcp (spillAlloc vcp) af fa fb K F G XI H base ra Kp cc P R s w₀ N →
          ∀ t, ReachN env { funcs := [] } cs t N → callNum t = 1 →
          ∀ j < N, ∃ u i info uses w r, OnCall (ArmStepX (XI.at 0) H fa) fa base s j u ∧
            spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧ CallSiteAt F K G s fa base i uses w u ∧
            (i = .call info ∨ ∃ ti, i = .tryCall info ti) ∧
            (XI.at j).call (callDest info) uses w = some r := by
  obtain ⟨hsub, vc, vcp, af, fa, fb, hc, hcov, -⟩ := compiled_covered_exists
  exact ⟨vc, vcp, af, fa, fb, hc, fun env XI K F c w₀ args cs hce hrel hargs htr N H G base ra Kp
    cc P R s he t hr hcn => backend_prefix_cleanupPRI hsub hc source_callsOne.1 source_callsOne.2
      (hcov _) (fun _ n _ => source_xcalls _ _ _ n) (fun n b h => by cases h) rfl hce hrel hargs htr
      he hr hcn⟩

end E2E.DeadCleanupWitness
