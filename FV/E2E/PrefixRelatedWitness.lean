import FV.E2E.PrefixRelated
import FV.E2E.BackendWorldCleanupIWitness

/-!
# Witnesses for `FV/E2E/PrefixRelated.lean`

`ExtSemI.relOnly` with an empty relation answers no call, with the full relation every call of
`XI`; `prefix_related_cleanupPRI` applies to the closed cleanup compilation of
`DeadCleanupWitness.source` (the entry premises, `NoRetCall` and the machine entry remain).
-/

namespace E2E.DeadCleanupWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

theorem relOnly_none (XI : ExtSemI) (n : Nat) (d : Option String) (uses : List CV)
    (w : Arm.ArmState) : ((XI.relOnly fun _ _ _ _ => False).at n).call d uses w = none := by
  cases h : ((XI.relOnly fun _ _ _ _ => False).at n).call d uses w with
  | none => rfl
  | some r => exact (relOnly_call_some h).1.elim

theorem relOnly_all (XI : ExtSemI) (n : Nat) (d : Option String) (uses : List CV)
    (w : Arm.ArmState) :
    ((XI.relOnly fun _ _ _ _ => True).at n).call d uses w = (XI.at n).call d uses w :=
  relOnly_call_of trivial

/-- **`prefix_related_cleanupPRI` applies** to the closed cleanup compilation of `source`. -/
theorem prefix_related_applies :
    ∃ vc vcp af fa fb, CompiledCleanup source 0 vc vcp (spillAlloc vcp) af fa fb ∧
      ∀ (env : Clif.Env) (XI : ExtSemI) (K : Nat) (F : BitVec 64 → Prop) (c : BitVec 64)
        (w₀ : Arm.ArmState) (args : List Clif.Val) (cs : Clif.State),
        NoRetCall env { funcs := [] } cs →
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
            (XI.at j).call (callDest info) uses w = some r ∧
            RelatedN env { funcs := [] } cs (source.externs.map (·.2)) (indSigs source)
              (RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
                source c) XI.sym j (callDest info) uses w := by
  obtain ⟨hsub, vc, vcp, af, fa, fb, hc, hcov, -⟩ := compiled_covered_exists
  exact ⟨vc, vcp, af, fa, fb, hc, fun env XI K F c w₀ args cs hnrc hce hrel hargs htr N H G base ra
    Kp cc P R s he t hr hcn => prefix_related_cleanupPRI hsub hc source_callsOne.1
      source_callsOne.2 (hcov _) hnrc (fun _ n _ => source_xcalls _ _ _ n)
      (fun n b h => by cases h) rfl hce hrel hargs htr he hr hcn⟩

end E2E.DeadCleanupWitness
