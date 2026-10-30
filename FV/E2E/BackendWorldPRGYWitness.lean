import FV.E2E.BackendWorldPRGY
import FV.E2E.BackendWorldPRBWitness
import FV.E2E.LinkArmProphDetWitness
import FV.E2E.LinkArmStage2Y

/-!
# Witnesses for the related-call guard (#692: `FV/E2E/ExtSemGuardRY.lean`,
`BackendWorldPRGY.lean`, `LinkArmStage2Y.lean`)

* `InvokedNWitness`: at the extern call of `sCall`: accepted results exist (`callPostNXR_sCall`,
  `callPostXR_sCall`), stage 1 for every `CallPostNXR`-guarded semantics (`hX_sCall_RXR`), `ext` of
  the guarded semantics of the undefined call semantics (`guardRXRI_ext_none`, `guardR_extV`).
* `DeadCleanupWitness.prgy_applies`, `prgy_pipeline_applies`: both `*_PRGY` theorems apply.
* `LinkArmThmPRBRWitness`: `XPBTGY_ext_Lu`.
-/

namespace E2E.InvokedNWitness

open Backend Backend.Proof CallPostExistsWitness

theorem callPostNXR_sCall (Γ : Rel) (f : Clif.Function) (c : BitVec 64)
    (sym : String → Int → BitVec 64) :
    ∀ d uses w, ∃ r, CallPostNXR envE PE sCall [extE] [] (RelW Γ f c) sym 0 d uses w r :=
  callPostNXR_exists invokedRetOk_sCall 0

theorem callPostXR_sCall (Γ : Rel) (f : Clif.Function) (c : BitVec 64)
    (sym : String → Int → BitVec 64) :
    ∀ d uses w, ∃ r, CallPostXR (envE.only (InvokedN envE PE sCall 0)) [extE] [] (RelW Γ f c) sym d uses w r :=
  callPostXR_exists_of (callPost_invokedN_exists (invokedRetOk_sCall 0))

theorem hX_sCall_RXR (XI : ExtSemI) (Γ : Rel) (f : Clif.Function) (c : BitVec 64) :
    ∀ s n, ReachN envE PE sCall s n →
      XCallsOk (envE.only (Clif.Invoked envE PE s)) [extE] (RelW Γ f c)
        ((XI.guardRI (CallPostNXR envE PE sCall [extE] [] (RelW Γ f c) XI.sym)).at n) ∧
      XCallsIndOk (envE.only (Clif.Invoked envE PE s)) [] (RelW Γ f c)
        ((XI.guardRI (CallPostNXR envE PE sCall [extE] [] (RelW Γ f c) XI.sym)).at n) :=
  hX_guardRXRI XI noRetCall_sCall invokedRetOk_sCall

/-- The call semantics without results. -/
def XNoneY : ExtSemI := { ExtSemI.const LinkArmProphDetWitness.Lu.Xb with call := fun _ _ _ _ => none }

theorem guardRXRI_ext_none (Γ : Rel) (f : Clif.Function) (c : BitVec 64) (n : Nat) :
    ∀ d uses w outs w',
      ((XNoneY.guardRI (CallPostNXR envE PE sCall [extE] [] (RelW Γ f c) XNoneY.sym)).at n).call
        d uses w = some (outs, w') →
      Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program :=
  guardRXRI_ext XNoneY n fun _ _ _ _ _ h _ => nomatch h

end E2E.InvokedNWitness

namespace E2E.DeadCleanupWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **Both `*_PRGY` theorems apply** to the closed cleanup compilation of `source`. -/
theorem prgy_applies :
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
            us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
            PrefixHold vals outs ∧ MemRel F (fun _ => none) cm w ∧ vc.RetsSite us ∧
            ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat)
              (cc : BitVec 64) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
              (s : Arm.ArmState),
              ActEntryPR vcp (spillAlloc vcp) af fa fb K F G XG H base ra Kp cc P R s w₀ →
              ∃ n, ActRet ra F G us outs w s (runX (ArmStepX (XG.at 0) H fa) n s) ∧
                PostTrace fa af base (ArmStepX (XG.at 0) H fa) s n) ∧
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
  exact backend_correct_world_cleanupPRGY (K := K) hsub hc (hcov _) hnrc hR
    (fun n b h => by cases h) rfl hce hrel hargs htr fuel

/-- **`backend_correct_world_pipelinePRGY` applies** (same instance, `CompiledEither.cleanup`). -/
theorem prgy_pipeline_applies : type_of% prgy_applies := by
  obtain ⟨hsub, vc, vcp, af, fa, fb, hc, hcov, -⟩ := compiled_covered_exists
  refine ⟨vc, vcp, af, fa, fb, hc, fun XI K F c w₀ args cs hce hrel hargs htr fuel => ?_⟩
  have hnrc : NoRetCall Clif.Env.empty { funcs := [] } cs :=
    noRetCall_of_linv (P := ({ funcs := [] } : Clif.Program).only source)
      (fun g hg => (List.mem_singleton.mp hg) ▸ source_linkFree)
      (fun _ h => nomatch h) (linv_entry hce)
  have hR : InvokedRetOk Clif.Env.empty { funcs := [] } cs (source.externs.map (·.2))
      (indSigs source) := fun _ _ _ _ _ _ _ _ hg _ => by simp [Clif.Env.empty] at hg
  exact backend_correct_world_pipelinePRGY (K := K) hsub (.cleanup hc) (hcov _) hnrc hR
    (fun n b h => by cases h) rfl hce hrel hargs htr fuel

end E2E.DeadCleanupWitness

namespace E2E.LinkArmThmPRBRWitness

open Backend Backend.Proof LinkArmProphDetWitness

theorem XPBTGY_ext_Lu (M : Nat) (g : Clif.Function) (F : BitVec 64 → Prop)
    (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (env : Clif.Env) (cs : Clif.State)
    (c : BitVec 64) (n : Nat) :
    ∀ d uses w outs w',
      ((Lu.XPBTGY (fun M _ => Lu.K M) M g F P R env cs c).at n).call d uses w = some (outs, w') →
      Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program :=
  Lu.XPBTGY_ext Lu_ok n

end E2E.LinkArmThmPRBRWitness
