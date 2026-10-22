import FV.Concurrency.IselMemMain

/-!
# Layer 2: isel with interference (T2h, #311, layer 2e)

* `seg_res`: every segment from a match has its result (`IselThread.SegRes`): a terminator
  (`IselThread.term_seg`), a pure statement (`IselThread.pure_seg`) or a memory statement
  (`IselMemMain.mem_seg`);
* **`isel_refines`**: from a match of the driver (`Driver.Match`), every run of the VCode thread
  semantics (`VTRun` under `csem`, events `cEvs`: reads return the environment's bytes) is
  realized, up to a prefix after which the CLIF thread has no step or is at an `atomic_cas` on
  read-only data (`IselThread.Stop`), by a run of the CLIF thread semantics (`CRun`):
  `ThreadRefine.Refines Maps` with no private location and the VCode's two-event steps as its
  atomic pairs (`StepPair`), by `IselThread.simRes_of_seg` and `CorrRefine.refines_of_corr`.
-/

namespace Concurrency.IselRefines

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread IselCheck CorrRefine ClifCStepTerm IselThread ThreadRefine

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
  {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {MR : MemRelT} {env : Clif.Env}
  {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {sb : Nat} {syms : String → Option Nat}

/-- **Every segment from a match has its result, with progress and the return covered**
(`IselThread.SegResR`). -/
theorem seg_resR (H : DriverHyp f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBl f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X) (s : Clif.State) (c : VState CV ArmState) (tr : List (List Ev))
    (cT : VConf CV ArmState) (hm : Match f ctx R gn bl A MR slots s c)
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run c) tr cT) :
    SegResR env p vc (csem F fc X) (cEvs F fc) (Match f ctx R gn bl A MR slots) s tr cT := by
  obtain ⟨b, k, ρ, w⟩ := c
  cases hbody : s.frame.body with
  | nil => exact term_segR H hchk hm hbody hr
  | cons stm rest =>
    cases hp : pureInst stm.inst
    · exact IselMemMain.mem_segR H hchk hMR hMRw hX hm hbody hp hr
    · exact pure_segR H hchk hm hbody hp hr

/-- **Every segment from a match has its result, with progress** (`IselThread.SegResP`). -/
theorem seg_resP (H : DriverHyp f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBl f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X) (s : Clif.State) (c : VState CV ArmState) (tr : List (List Ev))
    (cT : VConf CV ArmState) (hm : Match f ctx R gn bl A MR slots s c)
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run c) tr cT) :
    SegResP env p vc (csem F fc X) (cEvs F fc) (Match f ctx R gn bl A MR slots) s tr cT :=
  (seg_resR H hchk hMR hMRw hX s c tr cT hm hr).segResP

/-- **Every segment from a match has its result.** -/
theorem seg_res (H : DriverHyp f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBl f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X) (s : Clif.State) (c : VState CV ArmState) (tr : List (List Ev))
    (cT : VConf CV ArmState) (hm : Match f ctx R gn bl A MR slots s c)
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run c) tr cT) :
    SegRes env p vc (csem F fc X) (cEvs F fc) (Match f ctx R gn bl A MR slots) s tr cT :=
  (seg_resP H hchk hMR hMRw hX s c tr cT hm hr).segRes

/-- **Layer 2: isel with interference** (module doc). -/
theorem isel_refines (H : DriverHyp f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBl f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X) {s : Clif.State} {c : VState CV ArmState}
    (hm : Match f ctx R gn bl A MR slots s c) {tr : List (List Ev)} {cT : VConf CV ArmState}
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run c) tr cT) :
    ∃ n trS t ψ, n ≤ tr.length ∧ CRun env p (.run s) trS t ∧
      Refines Maps (fun _ => False) (StepPair (conv (tr.take n))) trS (conv (tr.take n)) ψ ∧
      (n = tr.length ∨ Stop env p t) := by
  obtain ⟨n, trS, t, hn, hrun, hcorr, hend⟩ :=
    simRes_of_seg (seg_res H hchk hMR hMRw hX) s c tr cT hm hr
  obtain ⟨ψ, href⟩ := refines_of_corr hcorr hrun.length_le
  exact ⟨n, trS, t, ψ, hn, hrun, href, hend⟩

end

end Concurrency.IselRefines
