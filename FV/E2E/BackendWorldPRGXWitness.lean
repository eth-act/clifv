import FV.E2E.BackendWorldPRGX
import FV.E2E.BackendWorldPRBWitness
import FV.E2E.LinkArmXPBTX
import FV.E2E.LinkArmTabCount
import FV.E2E.LinkArmThmPRBRWitness
import FV.E2E.LinkArmTableBWitness
import FV.E2E.LinkArmEnvOfB

/-!
# Witnesses for the program-keeping guard (#690) and the table count (`FV/E2E/ExtSemGuardRX.lean`,
`BackendWorldPRGX.lean`, `LinkArmXPBTX.lean`, `LinkArmTabCount.lean`)

* `InvokedNWitness`: at the extern call `call fn0()` of `sCall` (invocation `0`): accepted
  results that keep the program exist (`callPostNX_sCall`, through `callPostX_exists_of`,
  `callPost_fixW`), stage 1 for every `CallPostNX`-guarded semantics (`hX_sCall_RX`), `ext` of
  the guarded semantics of the undefined call semantics (`guardRXI_ext_none`, `guardR_ext`), and
  `relW_set_program_ok` (the guard's program fix keeps `RelW`).
* `DeadCleanupWitness.prgx_applies`, `prgx_pipeline_applies`: both `*_PRGX` theorems apply.
* `LinkArmThmPRBRWitness`: `XPBTGX_ext_Lu`; `tabUpTo_count_Lu`, `sumTo_congr_calls_Lu`.
-/

namespace E2E.InvokedNWitness

open Backend Backend.Proof CallPostExistsWitness

theorem callPostNX_sCall (Γ : Rel) (f : Clif.Function) (c : BitVec 64)
    (sym : String → Int → BitVec 64) :
    ∀ d uses w, ∃ r, CallPostNX envE PE sCall [extE] [] (RelW Γ f c) sym 0 d uses w r :=
  callPostNX_exists invokedRetOk_sCall 0

theorem callPost_fixW_sCall (Γ : Rel) (f : Clif.Function) (c : BitVec 64)
    (sym : String → Int → BitVec 64) (d : Option String) (uses : List CV) (w : Arm.ArmState) :
    ∃ r, CallPostX (envE.only (InvokedN envE PE sCall 0)) [extE] [] (RelW Γ f c) sym d uses w r :=
  let ⟨r, hr⟩ := callPost_invokedN_exists (invokedRetOk_sCall 0) (Γ := Γ) (f := f) (c := c)
    (sym := sym) d uses w
  ⟨_, callPost_fixW hr⟩

theorem hX_sCall_RX (XI : ExtSemI) (Γ : Rel) (f : Clif.Function) (c : BitVec 64) :
    ∀ s n, ReachN envE PE sCall s n →
      XCallsOk (envE.only (Clif.Invoked envE PE s)) [extE] (RelW Γ f c)
        ((XI.guardRI (CallPostNX envE PE sCall [extE] [] (RelW Γ f c) XI.sym)).at n) ∧
      XCallsIndOk (envE.only (Clif.Invoked envE PE s)) [] (RelW Γ f c)
        ((XI.guardRI (CallPostNX envE PE sCall [extE] [] (RelW Γ f c) XI.sym)).at n) :=
  hX_guardRXI XI noRetCall_sCall invokedRetOk_sCall

/-- The call semantics without results. -/
def XNone : ExtSemI := { ExtSemI.const LinkArmProphDetWitness.Lu.Xb with call := fun _ _ _ _ => none }

theorem guardRXI_ext_none (Γ : Rel) (f : Clif.Function) (c : BitVec 64) (n : Nat) :
    ∀ d uses w outs w',
      ((XNone.guardRI (CallPostNX envE PE sCall [extE] [] (RelW Γ f c) XNone.sym)).at n).call
        d uses w = some (outs, w') →
      Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program :=
  guardRXI_ext XNone n fun _ _ _ _ _ h _ => nomatch h

theorem relW_set_program_ok {Γ : Rel} {f : Clif.Function} {c : BitVec 64}
    {sl : List (Clif.SlotId × Nat)} {cm : Clif.Mem} {w : Arm.ArmState}
    (h : RelW Γ f c sl cm w) : RelW Γ f c sl cm (Arm.set_program w []) :=
  relW_set_program [] h

end E2E.InvokedNWitness

namespace E2E.DeadCleanupWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **Both `*_PRGX` theorems apply** to the closed cleanup compilation of `source`. -/
theorem prgx_applies :
    ∃ vc vcp af fa fb, CompiledCleanup source 0 vc vcp (spillAlloc vcp) af fa fb ∧
      ∀ (XI : ExtSemI) (K : Nat) (F : BitVec 64 → Prop) (c : BitVec 64)
        (w₀ : Arm.ArmState) (args : List Clif.Val) (cs : Clif.State),
        ClifEntry source args cs →
        RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩
          source c cs.frame.slots cs.mem w₀ →
        ArgsAtEntry F source.sig args w₀ →
        TrapsExplicit Clif.Env.empty ({ funcs := [] } : Clif.Program) cs → ∀ fuel,
        let XG := XI.guardRI (CallPostNX Clif.Env.empty { funcs := [] } cs
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
  exact backend_correct_world_cleanupPRGX (K := K) hsub hc (hcov _) hnrc hR
    (fun n b h => by cases h) rfl hce hrel hargs htr fuel

/-- **`backend_correct_world_pipelinePRGX` applies** (same instance, `CompiledEither.cleanup`). -/
theorem prgx_pipeline_applies : type_of% prgx_applies := by
  obtain ⟨hsub, vc, vcp, af, fa, fb, hc, hcov, -⟩ := compiled_covered_exists
  refine ⟨vc, vcp, af, fa, fb, hc, fun XI K F c w₀ args cs hce hrel hargs htr fuel => ?_⟩
  have hnrc : NoRetCall Clif.Env.empty { funcs := [] } cs :=
    noRetCall_of_linv (P := ({ funcs := [] } : Clif.Program).only source)
      (fun g hg => (List.mem_singleton.mp hg) ▸ source_linkFree)
      (fun _ h => nomatch h) (linv_entry hce)
  have hR : InvokedRetOk Clif.Env.empty { funcs := [] } cs (source.externs.map (·.2))
      (indSigs source) := fun _ _ _ _ _ _ _ _ hg _ => by simp [Clif.Env.empty] at hg
  exact backend_correct_world_pipelinePRGX (K := K) hsub (.cleanup hc) (hcov _) hnrc hR
    (fun n b h => by cases h) rfl hce hrel hargs htr fuel

end E2E.DeadCleanupWitness

namespace E2E.LinkArmThmPRBRWitness

open Backend Backend.Proof LinkArmProphDetWitness

theorem XPBTGX_ext_Lu (M : Nat) (g : Clif.Function) (F : BitVec 64 → Prop)
    (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (env : Clif.Env) (cs : Clif.State)
    (c : BitVec 64) (n : Nat) :
    ∀ d uses w outs w',
      ((Lu.XPBTGX (fun M _ => Lu.K M) M g F P R env cs c).at n).call d uses w = some (outs, w') →
      Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program :=
  Lu.XPBTGX_ext Lu_ok n

/-- Two tables of the empty prefix have the same count. -/
theorem tabUpTo_count_Lu (M : Nat) (g : Clif.Function) (s : Arm.ArmState)
    (ini ini' : Clif.SlotInit) {e : Nat} (h : Lu.TabUpTo M g s ini'.bytes ini'.next 0 e) : e = 0 :=
  (Lu.tabUpTo_count M g s ini'.bytes ini.bytes ini'.next ini.next 0 e 0 h
    (E2E.LinkArmTableBWitness.tab_Lu M g s ini))

theorem sumTo_congr_calls_Lu (M : Nat) (g : Clif.Function) (s : Arm.ArmState) :
    Clif.sumTo (fun _ => 1) (callsBefore (Lu.mach M g) (Lu.A g).fa (Lu.A g).base s 0) =
      Clif.sumTo (fun _ => 2) (callsBefore (Lu.mach M g) (Lu.A g).fa (Lu.A g).base s 0) :=
  LinkSys.sumTo_congr_calls 0 fun _ h => absurd h (Nat.not_lt_zero _)

/-- `envOfB` is `envR` on `Lu` (no slotted callees: the guard is vacuous). -/
theorem envOfB_envR_Lu (M : Nat) (g : Clif.Function) (c : BitVec 64) (n : String)
    (vals : List Clif.Val) (cm : Clif.Mem) :
    ((Lu.envOfB M g c).extern n).map (· vals cm) = ((Lu.envR M g).extern n).map (· vals cm) :=
  Lu.envOfB_envR vals fun h => absurd h noSlots_Lu

/-- **`runLoop_envOfB` on `Lu`**: from an activation state of `g` in its frame, the runs under
`envOfB` and `envR` agree. -/
theorem runLoop_envOfB_Lu (M : Nat) {g : Clif.Function} (hg : g ∈ Lu.P.funcs) (c : BitVec 64)
    (n : Nat) {s : Clif.State} (hI : Clif.LInv (Lu.P.only g) s) (hc : s.callers = []) :
    Clif.runLoop (Lu.envOfB M g c) Lu.P.bare n s = Clif.runLoop (Lu.envR M g) Lu.P.bare n s :=
  Lu.runLoop_envOfB Lu_ok hg n s ⟨hI, hc, fun h => absurd h noSlots_Lu⟩

theorem step_envOfB_Lu (M : Nat) {g : Clif.Function} (hg : g ∈ Lu.P.funcs) (c : BitVec 64)
    {s : Clif.State} (hI : Clif.LInv (Lu.P.only g) s) :
    Clif.step (Lu.envOfB M g c) Lu.P.bare s = Clif.step (Lu.envR M g) Lu.P.bare s :=
  Lu.step_envOfB (Lu_ok.free g hg) hI.1 fun h => absurd h noSlots_Lu

end E2E.LinkArmThmPRBRWitness
