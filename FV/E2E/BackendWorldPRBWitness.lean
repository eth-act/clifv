import FV.E2E.BackendWorldPRB
import FV.E2E.DeadCleanupWitness
import FV.E2E.TrapCallClifRun
import FV.E2E.CallPostExistsWitness

/-!
# Witnesses for `InvokedN` and the `*_PRB` theorems (SEM1 item (b), `docs/plans/uninit.md` §5.9)

* `InvokedNWitness`: a state `sCall` at `call fn0()` to the extern `e`: its invocation is
  `InvokedN … 0`, the scope conditions `NoRetCall` (from `LInv`) and `InvokedRetOk` hold, and
  `hX_guardI` gives the per-state contracts of any guarded semantics.
* `DeadCleanupWitness.prb_applies`: both `*_PRB` theorems apply to the closed cleanup compilation
  of `source` (no premise left but the entry ones).
-/

namespace E2E.InvokedNWitness

open Backend Backend.Proof CallPostExistsWitness

def stE : Clif.Stmt := { inst := .call 0 [] }

def blkE : Clif.Block := { id := 0, body := [stE], term := .ret [] }

/-- `call fn0()` (extern `e`), then `return`. -/
def fE : Clif.Function where
  name := "fE"
  sig := default
  externs := [(0, extE)]
  blocks := [blkE]

def frE : Clif.Frame where
  func := fE
  regs := Clif.Regs.empty
  slots := []
  body := [stE]
  term := .ret []

def sCall : Clif.State where
  frame := frE
  callers := []
  mem := Clif.Mem.empty

def PE : Clif.Program := { funcs := [fE] }

theorem invokedN_sCall : InvokedN envE PE sCall 0 "e" [] Clif.Mem.empty := by
  refine ⟨sCall, .refl, rfl, rfl, ?_⟩
  exact ⟨extE, rfl, rfl, rfl⟩

theorem noRetCall_sCall : NoRetCall envE PE sCall := by
  refine noRetCall_of_linv (P := PE) ?_ (fun _ h => h) ?_
  · intro g hg b hb fn args he
    simp only [PE, List.mem_singleton] at hg
    subst hg
    simp only [fE, List.mem_singleton] at hb
    subst hb
    cases he
  · exact ⟨⟨by simp [sCall, frE, PE], .inl ⟨blkE, by simp [sCall, frE, fE],
      List.suffix_refl _, rfl⟩⟩, fun _ h => nomatch h⟩

theorem invokedRetOk_sCall : InvokedRetOk envE PE sCall [extE] [] := by
  intro n nm vals m g rvals cm' _ hg hret
  unfold envE at hg
  dsimp only at hg
  split at hg
  · cases hg
    cases hret
    exact ⟨fun _ _ h => h, rfl, (sigRets extE.sig).length, Nat.zero_le _,
      fun ext hext _ _ _ => by simp only [List.mem_singleton] at hext; subst hext; rfl,
      fun _ h => nomatch h⟩
  · cases hg

/-- **`hX_guardI` applies**: every guarded semantics meets the per-state contracts of the run
from `sCall`. -/
theorem hX_sCall (XI : ExtSemI) (Γ : Rel) (f : Clif.Function) (c : BitVec 64) :
    ∀ s n, ReachN envE PE sCall s n →
      XCallsOk (envE.only (Clif.Invoked envE PE s)) [extE] (RelW Γ f c)
        ((XI.guardI (CallPostN envE PE sCall [extE] [] (RelW Γ f c) XI.sym)).at n) ∧
      XCallsIndOk (envE.only (Clif.Invoked envE PE s)) [] (RelW Γ f c)
        ((XI.guardI (CallPostN envE PE sCall [extE] [] (RelW Γ f c) XI.sym)).at n) :=
  hX_guardI XI noRetCall_sCall invokedRetOk_sCall

end E2E.InvokedNWitness

namespace E2E.DeadCleanupWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

theorem source_linkFree : Clif.LinkFree source := by
  have h : source.blocks.all (fun b => match b.term with | .returnCall .. => false | _ => true) =
      true := by decide
  intro b hb fn args he
  simp only [List.all_eq_true] at h
  have := h b hb
  rw [he] at this; simp at this

/-- **Both `*_PRB` theorems apply** to the closed cleanup compilation of `source`, with the
guarded semantics of any `XI` and the empty environment. -/
theorem prb_applies :
    ∃ vc vcp af fa fb, CompiledCleanup source 0 vc vcp (spillAlloc vcp) af fa fb ∧
      ∀ (XI : ExtSemI) (K : Nat) (F : BitVec 64 → Prop) (c : BitVec 64)
        (w₀ : Arm.ArmState) (args : List Clif.Val) (cs : Clif.State),
        ClifEntry source args cs →
        RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
          source c cs.frame.slots cs.mem w₀ →
        ArgsAtEntry F source.sig args w₀ →
        TrapsExplicit Clif.Env.empty ({ funcs := [] } : Clif.Program) cs → ∀ fuel,
        let XG := XI.guardI (CallPostN Clif.Env.empty { funcs := [] } cs
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
  exact backend_correct_world_cleanupPRB (K := K) hsub hc (hcov _) hnrc hR
    (fun n b h => by cases h) rfl hce hrel hargs htr fuel

/-- **`backend_correct_world_pipelinePRB` applies** (same instance, `CompiledEither.cleanup`). -/
theorem prb_pipeline_applies : type_of% prb_applies := by
  obtain ⟨hsub, vc, vcp, af, fa, fb, hc, hcov, -⟩ := compiled_covered_exists
  refine ⟨vc, vcp, af, fa, fb, hc, fun XI K F c w₀ args cs hce hrel hargs htr fuel => ?_⟩
  have hnrc : NoRetCall Clif.Env.empty { funcs := [] } cs :=
    noRetCall_of_linv (P := ({ funcs := [] } : Clif.Program).only source)
      (fun g hg => (List.mem_singleton.mp hg) ▸ source_linkFree)
      (fun _ h => nomatch h) (linv_entry hce)
  have hR : InvokedRetOk Clif.Env.empty { funcs := [] } cs (source.externs.map (·.2))
      (indSigs source) := fun _ _ _ _ _ _ _ _ hg _ => by simp [Clif.Env.empty] at hg
  exact backend_correct_world_pipelinePRB (K := K) hsub (.cleanup hc) (hcov _) hnrc hR
    (fun n b h => by cases h) rfl hce hrel hargs htr fuel

end E2E.DeadCleanupWitness
