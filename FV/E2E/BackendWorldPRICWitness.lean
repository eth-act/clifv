import FV.E2E.BackendWorldPRIC
import FV.E2E.BackendWorldCleanupIWitness

/-!
# Witnesses for the `*_PRIC` theorems (SEM1, `docs/plans/uninit.md` §5.9)

The closed cleanup compilation of `DeadCleanupWitness.source`: each of
`backend_correct_world_cleanupPRIC`, `backend_correct_world_pipelinePRIC` and
`backend_correct_world_ni_pipelinePRIC` applies with no call-count premise.
-/

namespace E2E.DeadCleanupWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **The three `*_PRIC` theorems apply** to the closed cleanup compilation of `source`. -/
theorem pric_applies :
    ∃ vc vcp af fa fb, CompiledCleanup source 0 vc vcp (spillAlloc vcp) af fa fb ∧
      ∀ (env : Clif.Env) (XI : ExtSemI) (K : Nat) (F : BitVec 64 → Prop) (c : BitVec 64)
        (w₀ : Arm.ArmState) (args : List Clif.Val) (cs : Clif.State),
        ClifEntry source args cs →
        RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
          source c cs.frame.slots cs.mem w₀ →
        ArgsAtEntry F source.sig args w₀ →
        TrapsExplicit env ({ funcs := [] } : Clif.Program) cs → ∀ fuel,
        ((∀ vals cm, Clif.runLoop env { funcs := [] } fuel cs = .returned vals cm →
          ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
            RetPins vals us ∧ us.length = outs.length ∧
            PrefixHold vals outs ∧ MemRel F (fun _ => none) cm w ∧ vc.RetsSite us ∧
            ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat)
              (cc : BitVec 64) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
              (s : Arm.ArmState),
              ActEntryPR vcp (spillAlloc vcp) af fa fb K F G XI H base ra Kp cc P R s w₀ →
              ∃ n, ActRet ra F G us outs w s (runX (ArmStepX (XI.at 0) H fa) n s) ∧
                PostTrace fa af base (ArmStepX (XI.at 0) H fa) s n) ∧
        (∀ c', Clif.runLoop env { funcs := [] } fuel cs = .trapped c' →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat)
            (cc : BitVec 64) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
            (s : Arm.ArmState),
            ActEntryPR vcp (spillAlloc vcp) af fa fb K F G XI H base ra Kp cc P R s w₀ →
            ∃ n, TrapAt fb base c' (runX (ArmStepX (XI.at 0) H fa) n s))) ∧
        ((∀ vals cm, Clif.runLoop env { funcs := [] } fuel cs = .returned vals cm →
          ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
            RetPins vals us ∧ us.length = outs.length ∧
            PrefixHold vals outs ∧ MemRel F (fun _ => none) cm w ∧ vc.RetsSite us ∧
            ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat)
              (cc : BitVec 64) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
              (s : Arm.ArmState),
              ActEntryPR vcp (spillAlloc vcp) af fa fb K F G XI H base ra Kp cc P R s w₀ →
              ∃ n, ActRet ra F G us outs w s (runX (ArmStepX (XI.at 0) H fa) n s) ∧
                PostTrace fa af base (ArmStepX (XI.at 0) H fa) s n) ∧
        (∀ c', Clif.runLoop env { funcs := [] } fuel cs = .trapped c' →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat)
            (cc : BitVec 64) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
            (s : Arm.ArmState),
            ActEntryPR vcp (spillAlloc vcp) af fa fb K F G XI H base ra Kp cc P R s w₀ →
            ∃ n, TrapAt fb base c' (runX (ArmStepX (XI.at 0) H fa) n s))) ∧
        (∀ vals cm, Clif.runLoop env { funcs := [] } fuel cs = .returned vals cm →
          ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
            RetPins vals us ∧ us.length = outs.length ∧
            PrefixHold vals outs ∧ MemRel F (fun _ => none) cm w) := by
  obtain ⟨hsub, vc, vcp, af, fa, fb, hc, hcov, -⟩ := compiled_covered_exists
  refine ⟨vc, vcp, af, fa, fb, hc, fun env XI K F c w₀ args cs hce hrel hargs htr fuel =>
    ⟨?_, ?_, fun vals cm hrun => ?_⟩⟩
  · exact backend_correct_world_cleanupPRIC hsub hc (hcov _) (fun _ n _ => source_xcalls _ _ _ n)
      (fun n b h => by cases h) rfl hce hrel hargs htr fuel
  · exact backend_correct_world_pipelinePRIC hsub (.cleanup hc) (hcov _)
      (fun _ n _ => source_xcalls _ _ _ n) (fun n b h => by cases h) rfl hce hrel hargs htr fuel
  · obtain ⟨us, outs, w, h1, h2, h3, h4, -⟩ :=
      backend_correct_world_ni_pipelinePRIC (K := K) (XI := XI) hsub (.cleanup hc) (hcov _)
        (fun _ n _ => source_xcalls _ _ _ n) (fun n b h => by cases h) rfl hce hrel hargs htr fuel
        vals cm hrun
    exact ⟨us, outs, w, h1, h2, h3, h4⟩

end E2E.DeadCleanupWitness
