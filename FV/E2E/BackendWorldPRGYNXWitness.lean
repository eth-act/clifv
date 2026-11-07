import FV.E2E.BackendWorldPRGYNX
import FV.E2E.BackendWorldPRBWitness

/-!
# Witness for the per-state trace at the return (`RegLevelCorrectPRSNX`, `BackendWorldPRGYNX`)

* `DeadCleanupWitness.prgyNX_pipeline_applies`: `backend_correct_world_pipelinePRGYNX` applies to
  the closed cleanup compilation of `DeadCleanupWitness.source` (`CompiledEither.cleanup`; the
  chain through `regLevelCorrect_world_value_worldPRSNX`).
-/

namespace E2E.DeadCleanupWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **`backend_correct_world_pipelinePRGYNX` applies** (`CompiledEither.cleanup`). -/
theorem prgyNX_pipeline_applies :
    ∃ vc vcp af fa fb, CompiledCleanup source 0 vc vcp (spillAlloc vcp) af fa fb ∧
      ∀ (XI : ExtSemI) (K : Nat) (F : BitVec 64 → Prop) (c : BitVec 64)
        (w₀ : Arm.ArmState) (args : List Clif.Val) (cs : Clif.State),
        ClifEntry source args cs →
        RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
          source c cs.frame.slots cs.mem w₀ →
        ArgsAtEntry F source.sig args w₀ →
        TrapsExplicit Clif.Env.empty ({ funcs := [] } : Clif.Program) cs → ∀ fuel,
        let XG := XI.guardRI (CallPostNXR Clif.Env.empty { funcs := [] } cs
          (source.externs.map (·.2)) (indSigs source)
          (RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
            source c) XI.sym)
        (∀ vals cm, Clif.runLoop Clif.Env.empty { funcs := [] } fuel cs = .returned vals cm →
          ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
            RetPins vals us ∧ us.length = outs.length ∧
            PrefixHold vals outs ∧ MemRel F (fun _ => none) cm w ∧ vc.RetsSite us ∧
            ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat)
              (cc : BitVec 64) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
              (s : Arm.ArmState),
              ActEntryPR vcp (spillAlloc vcp) af fa fb K F G XG H base ra Kp cc P R s w₀ →
              ∃ n, ActRet ra F G us outs w s (runX (ArmStepX (XG.at 0) H fa) n s) ∧
                PostTrace fa af base (ArmStepX (XG.at 0) H fa) s n ∧
                (∀ i < n, Arm.r .ERR (runX (ArmStepX (XG.at 0) H fa) i s) = .None ∧
                  (runX (ArmStepX (XG.at 0) H fa) i s).program = fb.program base) ∧
                (∀ i < n, ∃ m, actGoodX vcp (spillAlloc vcp) af fa fb base s (XG.at m) H K G
                  (GotV vcp) (runX (ArmStepX (XG.at 0) H fa) i s)) ∧
                ∃ u, ReachN Clif.Env.empty { funcs := [] } cs u
                    (callsBefore (ArmStepX (XG.at 0) H fa) fa base s n) ∧
                  Clif.step Clif.Env.empty { funcs := [] } u = .done vals cm) ∧
        (∀ c', Clif.runLoop Clif.Env.empty { funcs := [] } fuel cs = .trapped c' →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat)
            (cc : BitVec 64) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
            (s : Arm.ArmState),
            ActEntryPR vcp (spillAlloc vcp) af fa fb K F G XG H base ra Kp cc P R s w₀ →
            ∃ n, TrapAt fb base c' (runX (ArmStepX (XG.at 0) H fa) n s)) := by
  obtain ⟨hsub, vc, vcp, af, fa, fb, hc, hcov, -⟩ := compiled_covered_exists
  refine ⟨vc, vcp, af, fa, fb, hc, fun XI K F c w₀ args cs hce hrel hargs htr fuel => ?_⟩
  have hnrc : NoRetCall Clif.Env.empty { funcs := [] } cs :=
    noRetCall_of_linv (P := ({ funcs := [] } : Clif.Program).only source)
      (fun g hg => (List.mem_singleton.mp hg) ▸ source_linkFree)
      (fun _ h => nomatch h) (linv_entry hce)
  have hR : InvokedRetOk Clif.Env.empty { funcs := [] } cs (source.externs.map (·.2))
      (indSigs source) := fun _ _ _ _ _ _ _ _ hg _ => by simp [Clif.Env.empty] at hg
  exact backend_correct_world_pipelinePRGYNX (K := K) hsub (.cleanup hc) (hcov _) hnrc hR
    (fun n b h => by cases h) rfl hce hrel hargs htr fuel

end E2E.DeadCleanupWitness
