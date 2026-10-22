import FV.E2E.WorldUnwindNI
import FV.E2E.WorldUnwindWitness

/-!
# Non-vacuity of the per-function world theorem with unwinding and non-interference (S10f, #233)

`backend_correct_world_ni_pipelineU` applied to the `try_call` function of
`FV/E2E/DeadCleanupUnwindWitness.lean` compiled by both pipelines (the receipts of
`FV/E2E/WorldUnwindWitness.lean`), with raising callees (every extern unwinds,
`IselSimUWitness.env`; the callees' exceptional semantics raises object 77 and restores the call
state, `IselSimUWitness.XR`; no normally returning callee, `Xr`; TLSDESC flags independent of the
world, `X1`). Its non-interference premises hold — `XNI` and `XTls` (`xni`, `xtls`) and the
callees' non-interference on raises `XRNI` (`xrni`: the unwinder keeps the agreement) — so the
exceptional end of the CLIF run is realised, up to `F ∪ D`, by every activation entered with a
body-entry world related to the same CLIF entry agreeing outside `F ∪ D`: only the run's
premises are left.
-/

namespace E2E.WorldUnwindNIWitness

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.UnwindTables Backend.DeadCleanup
open DeadCleanupUnwindWitness WorldUnwindWitness

/-- An external semantics whose TLSDESC flags do not depend on the world. -/
def X1 (p0 : Arm.PState) : ExtSem := ⟨fun _ _ _ => none, fun _ _ => 0, 0, fun _ _ => p0⟩

/-- No callee returns normally: `XNI` holds. -/
theorem xni (X0 : ExtSem) (F : BitVec 64 → Prop) (syms : String → Option Nat)
    (exts : List Clif.ExtFunc) (sigs : List Clif.Signature) (c : BitVec 64)
    (Lg : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) :
    XNI F syms exts sigs c Lg (Xr X0) := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hx
  cases hx

theorem xtls (p0 : Arm.PState) (F : BitVec 64 → Prop) : XTls F (Xr (X1 p0)) :=
  fun _ _ _ _ _ _ => rfl

/-- **The raising callees keep the agreement** (`XRNI` for `IselSimUWitness.XR`: the unwinder
restores the call state). -/
theorem xrni (F : BitVec 64 → Prop) (syms : String → Option Nat) (exts : List Clif.ExtFunc)
    (sigs : List Clif.Signature) (c : BitVec 64)
    (Lg : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (X : ExtSem) :
    XRNI F syms exts sigs c Lg X IselSimUWitness.XR := by
  intro n sig vals cm args d uses Z w w' o x o' x' _ _ _ hsw _ _ _ _ _ hr hr'
  simp only [IselSimUWitness.XR, Option.some.injEq, Prod.mk.injEq] at hr hr'
  obtain ⟨-, rfl⟩ := hr
  obtain ⟨-, rfl⟩ := hr'
  exact hsw

/-- **`backend_correct_world_ni_pipelineU`'s non-interference clause applies to the `try_call`
function compiled by the dead-cleanup pipeline**: the exceptional end of its CLIF run is
realised, up to `F ∪ D`, by every activation entered with a related body-entry world `w₀'`. -/
theorem world_ni_applies (p0 : Arm.PState) {K : Nat} {F : BitVec 64 → Prop} {c : BitVec 64}
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry source args cs)
    (hrel : RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp rf).intBase⟩ source c
      cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F source.sig args w₀)
    (htr : TrapsExplicitX IselSimUWitness.env { funcs := [] } cs) (fuel : Nat) :
    ∀ e cm, Clif.runLoopX IselSimUWitness.env { funcs := [] } fuel cs.toX = .unwound e cm →
      ∃ (obj : BitVec 64) (w : Arm.ArmState), ExnRel e obj ∧ MemRel F (fun _ => none) cm w ∧
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, fun _ => none, af.slotBase, (RAFrame.compute vcp rf).intBase⟩ source c
            cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf source.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf source.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
            (s : Arm.ArmState),
            ActEntryU vcp rf af fa fb K F G (Xr (X1 p0)) H IselSimUWitness.XR U base ra s w₀' →
            ∃ n, ActUnw ra (fun a => F a ∨ D a) G obj w s
                (runX (Unw.ArmStepU (Xr (X1 p0)) H U T fa) n s) ∧
              PostTrace fa af base (Unw.ArmStepU (Xr (X1 p0)) H U T fa) s n ∧ 0 < n ∧
              UnwExit U T fa (runX (Unw.ArmStepU (Xr (X1 p0)) H U T fa) (n - 1) s) := by
  obtain ⟨hv, hs, -, hc, hlU, hsv, hpad, hlast, hcs', -, hrows⟩ := facts
  intro e cm hrun
  obtain ⟨obj, w, hex, hm, -, hni⟩ := (backend_correct_world_ni_pipelineU (X := Xr (X1 p0))
    (XR := IselSimUWitness.XR) (T := T) (K := K)
    (InSubset.of_verifiable hv (fun _ => rfl)) (.cleanup hc)
    hlU (formsCovered_cleanup_complete (lowerScope_of hs) hc.lower hc.prepare _)
    (xCallsOk_env _ _ _) (xCallsIndOk_env _ _ _)
    (IselSimUWitness.xRaiseOk _ _ _) (IselSimUWitness.xRaiseIndOk _ _ _)
    (fun _ _ _ h => absurd rfl h) (fun _ _ h => by cases h) rfl
    hcs' rfl hrows rfl rfl hpad hlast hsv hcs hrel hargs htr fuel).2.2 e cm hrun
  exact ⟨obj, w, hex, hm, hni (xni _ _ _ _ _ _ _) (xtls p0 F) (xrni _ _ _ _ _ _ _)⟩

/-- **The same for the legacy pipeline** (`csemU`). -/
theorem world_ni_applies_legacy (p0 : Arm.PState) {K : Nat} {F : BitVec 64 → Prop}
    {c : BitVec 64} {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry source args cs)
    (hrel : RelW ⟨F, fun _ => none, afL.slotBase, (RAFrame.compute vcpL rfL).intBase⟩ source c
      cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F source.sig args w₀)
    (htr : TrapsExplicitX IselSimUWitness.env { funcs := [] } cs) (fuel : Nat) :
    ∀ e cm, Clif.runLoopX IselSimUWitness.env { funcs := [] } fuel cs.toX = .unwound e cm →
      ∃ (obj : BitVec 64) (w : Arm.ArmState), ExnRel e obj ∧ MemRel F (fun _ => none) cm w ∧
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, fun _ => none, afL.slotBase, (RAFrame.compute vcpL rfL).intBase⟩ source c
            cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf source.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf source.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (U : Unw.UnwHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
            (s : Arm.ArmState),
            ActEntryU vcpL rfL afL faL fbL K F G (Xr (X1 p0)) H IselSimUWitness.XR U base ra s w₀' →
            ∃ n, ActUnw ra (fun a => F a ∨ D a) G obj w s
                (runX (Unw.ArmStepU (Xr (X1 p0)) H U TL faL) n s) ∧
              PostTrace faL afL base (Unw.ArmStepU (Xr (X1 p0)) H U TL faL) s n ∧ 0 < n ∧
              UnwExit U TL faL (runX (Unw.ArmStepU (Xr (X1 p0)) H U TL faL) (n - 1) s) := by
  obtain ⟨hv, hs, -, -, hlU, -⟩ := facts
  obtain ⟨hc, hsv, hpad, hlast, hcs', hrows⟩ := factsL
  intro e cm hrun
  obtain ⟨obj, w, hex, hm, -, hni⟩ := (backend_correct_world_ni_pipelineU (X := Xr (X1 p0))
    (XR := IselSimUWitness.XR) (T := TL) (K := K)
    (InSubset.of_verifiable hv (fun _ => rfl)) (.legacy hc)
    hlU (formsCovered_completeB hs hc.lower hc.prepare _)
    (xCallsOk_env _ _ _) (xCallsIndOk_env _ _ _)
    (IselSimUWitness.xRaiseOk _ _ _) (IselSimUWitness.xRaiseIndOk _ _ _)
    (fun _ _ _ h => absurd rfl h) (fun _ _ h => by cases h) rfl
    hcs' rfl hrows rfl rfl hpad hlast hsv hcs hrel hargs htr fuel).2.2 e cm hrun
  exact ⟨obj, w, hex, hm, hni (xni _ _ _ _ _ _ _) (xtls p0 F) (xrni _ _ _ _ _ _ _)⟩

end E2E.WorldUnwindNIWitness
