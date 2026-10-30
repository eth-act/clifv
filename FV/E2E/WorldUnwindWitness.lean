import FV.E2E.WorldUnwind
import FV.Backend.Proof.FormsCoverComplete
import FV.E2E.DeadCleanupUnwindWitness

/-!
# Non-vacuity of the per-function world theorem with unwinding (S10f, #233)

`backend_correct_world_pipelineU` applied to the `try_call` function of
`FV/E2E/DeadCleanupUnwindWitness.lean` compiled by both pipelines: the dead-cleanup one (that
file's closed receipt) and the legacy one (`checksL_true`, the same convention), with raising
callees (every extern unwinds with a Rust panic, `IselSimUWitness.env`; the callees' exceptional
semantics raises object 77, `IselSimUWitness.XR`; no normally returning callee, `Xr X0`): only
the run's premises (the CLIF entry, the memory relation, the arguments, `TrapsExplicitX`) are
left. The raising callees' contract of `ActEntryU` holds for the machine's raising callees `Uw`
at every activation (`unw_holds`).
-/

namespace E2E.WorldUnwindWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.UnwindTables Backend.DeadCleanup
open DeadCleanupUnwindWitness

/-- **`backend_correct_world_pipelineU` applies to the `try_call` function compiled by the
dead-cleanup pipeline**: an exceptional end of its CLIF run is realised by every activation
(`ActUnw`, `PostTrace`, the last step leaving the frame by unwinding). -/
theorem world_applies {X0 : ExtSem} {K : Nat} {F : BitVec 64 → Prop} {c : BitVec 64}
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry source args cs)
    (hrel : RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp rf).intBase⟩ source c
      cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F source.sig args w₀)
    (htr : TrapsExplicitX IselSimUWitness.env { funcs := [] } cs) (fuel : Nat) :
    ∀ e cm, Clif.runLoopX IselSimUWitness.env { funcs := [] } fuel cs.toX = .unwound e cm →
      ∃ (obj : BitVec 64) (w : Arm.ArmState), ExnRel e obj ∧ MemRel F (fun _ => none) cm w ∧
        ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState),
          ActEntryU vcp rf af fa fb K F G (Xr X0) H IselSimUWitness.XR U base ra s w₀ →
          ∃ n, ActUnw ra F G obj w s (runX (Unw.ArmStepU (Xr X0) H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU (Xr X0) H U T fa) s n ∧ 0 < n ∧
            UnwExit U T fa (runX (Unw.ArmStepU (Xr X0) H U T fa) (n - 1) s) := by
  obtain ⟨hv, hs, -, hc, hlU, hsv, hpad, hlast, hcs', -, hrows⟩ := facts
  exact (backend_correct_world_pipelineU (InSubset.of_verifiable hv (fun _ => rfl)) (.cleanup hc)
    hlU (formsCovered_cleanup_complete (lowerScope_of hs) hc.lower hc.prepare _)
    (xCallsOk_env _ _ _) (xCallsIndOk_env _ _ _)
    (IselSimUWitness.xRaiseOk _ _ _) (IselSimUWitness.xRaiseIndOk _ _ _)
    (fun _ _ _ h => absurd rfl h) (fun _ _ h => by cases h) rfl
    hcs' rfl hrows rfl rfl hpad hlast hsv hcs hrel hargs htr fuel).2.2

/-- **`backend_correct_world_pipelineUG` applies to the `try_call` function compiled by the
dead-cleanup pipeline**: an exceptional end of its CLIF run is realised by every activation, every
state before the end with the per-state facts with unwinding (`actGoodXU`). -/
theorem world_appliesG {X0 : ExtSem} {K : Nat} {F : BitVec 64 → Prop} {c : BitVec 64}
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry source args cs)
    (hrel : RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp rf).intBase⟩ source c
      cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F source.sig args w₀)
    (htr : TrapsExplicitX IselSimUWitness.env { funcs := [] } cs) (fuel : Nat) :
    ∀ e cm, Clif.runLoopX IselSimUWitness.env { funcs := [] } fuel cs.toX = .unwound e cm →
      ∃ (obj : BitVec 64) (w : Arm.ArmState), ExnRel e obj ∧ MemRel F (fun _ => none) cm w ∧
        ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState),
          ActEntryU vcp rf af fa fb K F G (Xr X0) H IselSimUWitness.XR U base ra s w₀ →
          ∃ n, ActUnw ra F G obj w s (runX (Unw.ArmStepU (Xr X0) H U T fa) n s) ∧
            PostTrace fa af base (Unw.ArmStepU (Xr X0) H U T fa) s n ∧ 0 < n ∧
            UnwExit U T fa (runX (Unw.ArmStepU (Xr X0) H U T fa) (n - 1) s) ∧
            ∀ i < n, actGoodXU vcp rf af fa fb base s (Xr X0) H IselSimUWitness.XR U T K G
              (GotV vcp) (runX (Unw.ArmStepU (Xr X0) H U T fa) i s) := by
  obtain ⟨hv, hs, -, hc, hlU, hsv, hpad, hlast, hcs', -, hrows⟩ := facts
  exact (backend_correct_world_pipelineUG (InSubset.of_verifiable hv (fun _ => rfl)) (.cleanup hc)
    hlU (formsCovered_cleanup_complete (lowerScope_of hs) hc.lower hc.prepare _)
    (xCallsOk_env _ _ _) (xCallsIndOk_env _ _ _)
    (IselSimUWitness.xRaiseOk _ _ _) (IselSimUWitness.xRaiseIndOk _ _ _)
    (fun _ _ _ h => absurd rfl h) (fun _ _ h => by cases h) rfl
    hcs' rfl hrows rfl rfl hpad hlast hsv hcs hrel hargs htr fuel).2.2

/-- The raising callees' contract of `ActEntryU` holds for `Uw` at every activation. -/
theorem unw_holds (X0 : ExtSem) (K : Nat) (F G : BitVec 64 → Prop) (s : Arm.ArmState)
    (base : BitVec 64) :
    CalleeUnwOkG F K G s (CallAt fa base) (Xr X0) IselSimUWitness.XR Uw vcp.CallSite (GotV vcp) :=
  calleeUnwOkG_raise F K G s _ X0 _ _

/-! ## The legacy pipeline -/

/-- The legacy pipeline's outputs (`prepare` of the lowering output, no cleanup). -/
def vcpL : VCode := (Backend.prepare vc).toOption.getD default
def rfL : RFunc := spillAlloc vcpL
def afL : AFunc := (lowerRFunc vcpL rfL).toOption.getD default
def faL : FnAsm := (emitFunc 0 afL).toOption.getD default
def fbL : FnBin := faL.layout.toOption.getD default
def lsdaL : Option (List CallSite) := (callSites afL faL).toOption.getD none
def rowsL : List (Nat × Cfi) := (unwindRows afL faL).toOption.getD []

/-- Its tables. -/
def TL : Unw.FnTables := ⟨cieInsns, insnsFrom 0 rowsL, lsdaL.map (List.map (·.entry))⟩

/-- **The closed receipt of the legacy pipeline.** -/
def checksL : Bool :=
  (lowerFunction source).toBool && (Backend.prepare vc).toBool && prepCheck vc vcpL &&
  (checkAlloc vcpL rfL).toBool && (lowerRFunc vcpL rfL).toBool && (emitFunc 0 afL).toBool &&
  faL.layout.toBool && savedCheck vcpL rfL && padsNonzeroB afL faL && lastCallsOk afL faL &&
  (callSites afL faL).toBool && lsdaL.isSome && (unwindRows afL faL).toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The legacy pipeline on the witness function (the convention of
`DeadCleanupWitness.checks_true`); not used by any compiler correctness theorem. -/
theorem checksL_true : checksL = true := by native_decide

theorem factsL :
    Compiled source 0 vc vcpL rfL afL faL fbL ∧ savedCheck vcpL rfL = true ∧
    padsNonzeroB afL faL = true ∧ lastCallsOk afL faL = true ∧
    callSites afL faL = .ok lsdaL ∧ unwindRows afL faL = .ok rowsL := by
  have h := checksL_true
  simp only [checksL, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hl, hp, hpc, hca, hal, hem, hla, hsv, hpad, hlast, hcs, -, hrows⟩ := h
  have hlU := (facts).2.2.2.2.1
  exact ⟨⟨ok_getD hl, lowerCheck_of_U hlU, ok_getD hp, hpc, ok_unit hca, ok_getD hal,
    ok_getD hem, ok_getD hla⟩, hsv, hpad, hlast, ok_getD hcs, ok_getD hrows⟩

/-- **`backend_correct_world_pipelineU` applies to the `try_call` function compiled by the legacy
pipeline.** -/
theorem world_applies_legacy {X0 : ExtSem} {K : Nat} {F : BitVec 64 → Prop} {c : BitVec 64}
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry source args cs)
    (hrel : RelW ⟨F, fun _ => none, afL.slotBase, (RAFrame.compute vcpL rfL).intBase⟩ source c
      cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F source.sig args w₀)
    (htr : TrapsExplicitX IselSimUWitness.env { funcs := [] } cs) (fuel : Nat) :
    ∀ e cm, Clif.runLoopX IselSimUWitness.env { funcs := [] } fuel cs.toX = .unwound e cm →
      ∃ (obj : BitVec 64) (w : Arm.ArmState), ExnRel e obj ∧ MemRel F (fun _ => none) cm w ∧
        ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
          (s : Arm.ArmState),
          ActEntryU vcpL rfL afL faL fbL K F G (Xr X0) H IselSimUWitness.XR U base ra s w₀ →
          ∃ n, ActUnw ra F G obj w s (runX (Unw.ArmStepU (Xr X0) H U TL faL) n s) ∧
            PostTrace faL afL base (Unw.ArmStepU (Xr X0) H U TL faL) s n ∧ 0 < n ∧
            UnwExit U TL faL (runX (Unw.ArmStepU (Xr X0) H U TL faL) (n - 1) s) := by
  obtain ⟨hv, hs, -, -, hlU, -⟩ := facts
  obtain ⟨hc, hsv, hpad, hlast, hcs', hrows⟩ := factsL
  exact (backend_correct_world_pipelineU (InSubset.of_verifiable hv (fun _ => rfl)) (.legacy hc)
    hlU (formsCovered_completeB hs hc.lower hc.prepare _)
    (xCallsOk_env _ _ _) (xCallsIndOk_env _ _ _)
    (IselSimUWitness.xRaiseOk _ _ _) (IselSimUWitness.xRaiseIndOk _ _ _)
    (fun _ _ _ h => absurd rfl h) (fun _ _ h => by cases h) rfl
    hcs' rfl hrows rfl rfl hpad hlast hsv hcs hrel hargs htr fuel).2.2

end E2E.WorldUnwindWitness
