import FV.E2E.CompiledEitherI
import FV.E2E.BackendWorldNII
import FV.E2E.DeadCleanupWitness
import FV.E2E.ClifEnvOnlyContracts

/-!
# Non-vacuity of the counted cleanup pipeline (SEM1, `docs/plans/uninit.md` §5.9)

`DeadCleanupWitness.source` (a real function compiled through the dead-code cleanup, which removes
an instruction) satisfies the function-level premises of `iselSim_relWI_cleanup` and
`backend_correct_world_cleanupPRI`: the call counts (no call statement, no `try_call`), the callee
contracts at every index (no externs, no indirect call), the form coverage.

* `source_callsOne`, `source_xcalls`;
* `cleanupPRI_applies`: for the closed compilation of `source`, `backend_correct_world_cleanupPRI`'s
  conclusion from the entry premises alone.
-/

namespace E2E.DeadCleanupWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- `source`'s call counts: no call statement, no `try_call`. -/
theorem source_callsOne : InstCallsOne source ∧ TryCallsOne source := by
  refine ⟨?_, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨B, hB, ht⟩ => ?_,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨B, hB, ht⟩ => ?_⟩
  · intro _ _ _ inst _ _ _ _ _ ⟨B, hB, stm, hstm, hi⟩ _ _ _ _ _ _ _ hcl
    simp only [source, List.mem_singleton] at hB
    subst hB
    simp only [List.mem_singleton] at hstm
    subst hstm
    subst hi
    cases hcl
  · simp only [source, List.mem_singleton] at hB; subst hB; cases ht
  · simp only [source, List.mem_singleton] at hB; subst hB; cases ht

/-- `source`'s callee contracts (no externs, no indirect call), at every index. -/
theorem source_xcalls (env' : Clif.Env) (MR : MemRelT) (XI : ExtSemI) (n : Nat) :
    XCallsOk env' (source.externs.map (·.2)) MR (XI.at n) ∧
      XCallsIndOk env' (indSigs source) MR (XI.at n) := by
  refine ⟨fun ext hin => by simp [source] at hin, ?_⟩
  have : indSigs source = [] := by decide
  rw [this]
  exact xCallsIndOk_nil _ _ _

/-- **`backend_correct_world_cleanupPRI` applies** to the closed cleanup compilation of
`source` (the entry premises remain), here through `backend_correct_world_pipelinePRI` with the
artifact `CompiledEither.cleanup`. -/
theorem cleanupPRI_applies :
    ∃ vc vcp af fa fb, CompiledCleanup source 0 vc vcp (spillAlloc vcp) af fa fb ∧
      ∀ (env : Clif.Env) (XI : ExtSemI) (K : Nat) (F : BitVec 64 → Prop) (c : BitVec 64)
        (w₀ : Arm.ArmState) (args : List Clif.Val) (cs : Clif.State),
        ClifEntry source args cs →
        RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
          source c cs.frame.slots cs.mem w₀ →
        ArgsAtEntry F source.sig args w₀ →
        TrapsExplicit env ({ funcs := [] } : Clif.Program) cs → ∀ fuel,
        (∀ vals cm, Clif.runLoop env { funcs := [] } fuel cs = .returned vals cm →
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
            ∃ n, TrapAt fb base c' (runX (ArmStepX (XI.at 0) H fa) n s)) := by
  obtain ⟨hsub, vc, vcp, af, fa, fb, hc, hcov, -⟩ := compiled_covered_exists
  refine ⟨vc, vcp, af, fa, fb, hc, fun env XI K F c w₀ args cs hce hrel hargs htr fuel => ?_⟩
  exact backend_correct_world_pipelinePRI hsub (.cleanup hc) source_callsOne.1 source_callsOne.2
    (hcov _) (fun _ n _ => source_xcalls _ _ _ n) (fun n b h => by cases h) rfl hce hrel
    hargs htr fuel

/-- `source` admits no call (no externs, no indirect call): `XNI` holds at every index. -/
theorem source_xni (env' : Clif.Env) (F : BitVec 64 → Prop) (syms : String → Option Nat)
    (c : BitVec 64) (X : ExtSem) :
    XNI F syms (source.externs.map (·.2)) (indSigs source) c
      (CallLg env' (source.externs.map (·.2)) (indSigs source)) X := by
  have : indSigs source = [] := by decide
  rintro n sig vals cm _ _ _ _ _ _ _ _ _ _ ⟨hk, -⟩
  rw [this] at hk
  rcases hk with ⟨e, he, -⟩ | ⟨hs, -⟩
  · simp [source] at he
  · simp at hs

/-- **The premises of `backend_correct_world_ni_pipelinePRI` are jointly satisfied** by the
closed cleanup compilation of `source`, including the non-interference clause's `XNI` (every
index, the restricted environment), and the theorem applies. -/
theorem ni_pipelinePRI_applies :
    ∃ vc vcp af fa fb, CompiledEither source 0 vc vcp (spillAlloc vcp) af fa fb ∧
      InstCallsOne source ∧ TryCallsOne source ∧ FormsCovered ⟨fa.k, af.slotBase⟩ vcp ∧
      (∀ (env : Clif.Env) (XI : ExtSemI) (F : BitVec 64 → Prop) (c : BitVec 64) cs s n,
        ReachN env ({ funcs := [] } : Clif.Program) cs s n →
        XNI F (fun _ => none) (source.externs.map (·.2)) (indSigs source) c
          (CallLg (env.only (Clif.Invoked env { funcs := [] } s)) (source.externs.map (·.2))
            (indSigs source)) (XI.at n)) ∧
      ∀ (env : Clif.Env) (XI : ExtSemI) (K : Nat) (F : BitVec 64 → Prop) (c : BitVec 64)
        (w₀ : Arm.ArmState) (args : List Clif.Val) (cs : Clif.State),
        ClifEntry source args cs →
        RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
          source c cs.frame.slots cs.mem w₀ →
        ArgsAtEntry F source.sig args w₀ →
        TrapsExplicit env ({ funcs := [] } : Clif.Program) cs → ∀ fuel vals cm,
        Clif.runLoop env { funcs := [] } fuel cs = .returned vals cm →
        ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
          RetPins vals us ∧ us.length = outs.length ∧
          PrefixHold vals outs ∧ MemRel F (fun _ => none) cm w := by
  obtain ⟨hsub, vc, vcp, af, fa, fb, hc, hcov, -⟩ := compiled_covered_exists
  refine ⟨vc, vcp, af, fa, fb, .cleanup hc, source_callsOne.1, source_callsOne.2, hcov _,
    fun env XI F c cs s n _ => source_xni _ _ _ _ _,
    fun env XI K F c w₀ args cs hce hrel hargs htr fuel vals cm hrun => ?_⟩
  obtain ⟨us, outs, w, h1, h2, h3, h4, -⟩ :=
    backend_correct_world_ni_pipelinePRI (K := K) (XI := XI) hsub (.cleanup hc) source_callsOne.1
      source_callsOne.2 (hcov _) (fun _ n _ => source_xcalls _ _ _ n) (fun n b h => by cases h)
      rfl hce hrel hargs htr fuel vals cm hrun
  exact ⟨us, outs, w, h1, h2, h3, h4⟩

/-- The restriction lemmas on `source`: its contracts and `XNI` for the Rust environment give
those of every restriction of it (`xCallsOk_only`, `xCallsIndOk_only`, `xNI_only`), e.g. to the
invocation of a CLIF state. -/
theorem source_only (A : String → List Clif.Val → Clif.Mem → Prop) (MR : MemRelT) (X : ExtSem)
    (F : BitVec 64 → Prop) (c : BitVec 64) :
    XCallsOk (Clif.Rust.env.only A) (source.externs.map (·.2)) MR X ∧
      XCallsIndOk (Clif.Rust.env.only A) (indSigs source) MR X ∧
      XNI F (fun _ => none) (source.externs.map (·.2)) (indSigs source) c
        (CallLg (Clif.Rust.env.only A) (source.externs.map (·.2)) (indSigs source)) X :=
  ⟨xCallsOk_only A (source_xcalls Clif.Rust.env MR (ExtSemI.const X) 0).1,
    xCallsIndOk_only A (source_xcalls Clif.Rust.env MR (ExtSemI.const X) 0).2,
    xNI_only A (source_xni Clif.Rust.env F _ c X)⟩

end E2E.DeadCleanupWitness
