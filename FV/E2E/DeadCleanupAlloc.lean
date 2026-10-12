import FV.E2E.AllocTotal
import FV.E2E.DeadCleanupFinal
import FV.E2E.DeadCleanupCover
import FV.E2E.DeadCleanupCtl
import FV.Backend.Proof.DeadCleanupClasses
import FV.Backend.Proof.DeadCleanupEdgesOk
import FV.Backend.Proof.DeadCleanupKill
import FV.Backend.Proof.KillPrep

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Backend.DeadCleanup

/-- The existing spill allocator's local contracts after cleanup. -/
theorem spillLocal_cleanup {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode}
    (hsub : InSubset p f) (har : Spill.ArityOk f) (hd : Dominated f) (hs : LowerScope f)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare (prune vc) = .ok vcp) :
    Spill.SpillLocalOk vcp := by
  have hdom := prune_prepDomain (prepDomain_of_lower hs hl hs.nonempty)
  refine ⟨fun b vb k i hb hi => ?_,
    Spill.classesOk_of (Spill.classesOkM_prepare hp hdom
      (prune_classes (Spill.classesOkM_lower hs hl))),
    Spill.edgesOk_prepare (prune_lowOk (Spill.lowOk_of hd hs har hl)) hp⟩
  cases ht : i.isCtl
  · have hcov := formsCovered_cleanup_complete hs hl hp default b vb k i hb hi
    rw [ht] at hcov
    exact Spill.spillInstOk_of_formOk (hcov.resolve_left (by simp))
  · apply Spill.spillCtl_of_prepare hp hdom _ b vb k i hb hi ht
    exact prune_insts (ctlSpillHyp hsub hd hs hl)

/-- Cleanup keeps the killed-register availability condition used by the
existing spill correctness proof. -/
theorem spillKillFree_cleanup {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode}
    (hsub : InSubset p f) (har : Spill.ArityOk f) (hd : Dominated f) (hs : LowerScope f)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare (prune vc) = .ok vcp) :
    Spill.killFreeB vcp = true := by
  exact Spill.killFreeB_prepare (prune_lowOk (Spill.lowOk_of hd hs har hl))
    (prune_killFree (Kill.killFreeB_lower Kill.killRunsHyp Kill.tryDefsExact hd hs
      (abiSigsOk_of_inSubset hsub) har hl)) hp

/-- Spill allocation is checked with the same source conditions as before. -/
theorem spillAccepted_cleanup {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode}
    (hsub : InSubset p f) (har : Spill.ArityOk f) (hd : Dominated f) (hs : LowerScope f)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare (prune vc) = .ok vcp) :
    AllocChecked vcp (spillAlloc vcp) := by
  have hdom := prune_prepDomain (prepDomain_of_lower hs hl hs.nonempty)
  have hedge := Spill.edgesOk_prepare (prune_lowOk (Spill.lowOk_of hd hs har hl)) hp
  exact Spill.spillStep4 vcp (Spill.killD vcp) (Spill.cfg_ok_of_prepare hp hdom)
    (spillLocal_cleanup hsub har hd hs hl hp)
    (Spill.spillAvail_of_killFree (spillKillFree_cleanup hsub har hd hs hl hp) hedge)

/-- Lowering the spill allocation remains total on the old input scope. -/
theorem lowerRFunc_spillAlloc_cleanup {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode}
    (hsub : InSubset p f) (har : Spill.ArityOk f) (hd : Dominated f) (hs : LowerScope f)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare (prune vc) = .ok vcp) :
    ∃ af, lowerRFunc vcp (spillAlloc vcp) = .ok af := by
  obtain ⟨ss, ps, hc⟩ := Spill.cfg_ok_of_prepare hp
    (prune_prepDomain (prepDomain_of_lower hs hl hs.nonempty))
  obtain ⟨hi, h0⟩ := ctlInsts_cleanup_pipeline hsub hd hs hl hp
  exact lowerRFunc_spill_of hc (spillLocal_cleanup hsub har hd hs hl hp) hi h0

/-- Any regalloc2 answer has a successfully lowered fallback, as before. -/
theorem lowerAlloc_cleanup_total {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode}
    (hsub : InSubset p f) (har : Spill.ArityOk f) (hd : Dominated f) (hs : LowerScope f)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare (prune vc) = .ok vcp)
    (ra : Except String RFunc) : ∃ af, lowerAlloc vcp ra = .ok af := by
  rw [lowerAlloc_eq_lowerRFunc]
  have hsp := lowerRFunc_spillAlloc_cleanup hsub har hd hs hl hp
  unfold allocResult
  cases ra with
  | error e => exact hsp
  | ok rf =>
    simp only
    by_cases hc : (checkAlloc vcp rf).isOk = true
    · simp only [hc, ite_true]
      cases hlr : lowerRFunc vcp rf with
      | ok af => exact ⟨af, hlr⟩
      | error e => exact hsp
    · simp only [hc]; exact hsp

theorem allocChecked_allocResult_cleanup {p : Clif.Program} {f : Clif.Function}
    {vc vcp : VCode} (hsub : InSubset p f) (har : Spill.ArityOk f) (hd : Dominated f)
    (hs : LowerScope f) (hl : lowerFunction f = .ok vc) (hp : Backend.prepare (prune vc) = .ok vcp)
    (ra : Except String RFunc) : AllocChecked vcp (allocResult vcp ra) := by
  unfold allocResult
  cases ra with
  | error _ => exact spillAccepted_cleanup hsub har hd hs hl hp
  | ok rf =>
    simp only
    by_cases hc : (checkAlloc vcp rf).isOk = true
    · simp only [hc, ite_true]
      cases hlr : lowerRFunc vcp rf with
      | ok af =>
        cases h : checkAlloc vcp rf with
        | ok u => exact allocChecked_of_checkAlloc h
        | error e => rw [h] at hc; cases hc
      | error e => exact spillAccepted_cleanup hsub har hd hs hl hp
    · simp only [hc]; exact spillAccepted_cleanup hsub har hd hs hl hp

end E2E
