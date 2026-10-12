import FV.E2E.SpillCtlCheck
import FV.Backend.Proof.DeadCleanupPrepare
import FV.Backend.Proof.DeadCleanupPositions

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.DeadCleanup

private theorem clean_ctl {vc : VCode}
    (hv : ∀ b vb k i, vc.blocks[b]? = some vb → vb.insts[k]? = some i →
      CtlNA i ∨ (b = 0 ∧ k = 0 ∧ ArgsOk i)) :
    ∀ b vb k i, (clean vc).blocks[b]? = some vb → vb.insts[k]? = some i →
      CtlNA i ∨ (b = 0 ∧ k = 0 ∧ ArgsOk i) := by
  intro b vb k i hb hi
  rw [clean_blocks_map, Array.getElem?_map] at hb
  obtain ⟨old, hb0, rfl⟩ := Option.map_eq_some_iff.mp hb
  have h := scan_positions vc.classes.size old.insts.toList (exitLive vc 0 old)
    CtlNA (fun i => b = 0 ∧ ArgsOk i)
    (fun j i hj => by
      rcases hv b old j i hb0 (by simpa using hj) with h | ⟨h0, hj, ha⟩
      · exact .inl h
      · exact .inr ⟨hj, h0, ha⟩)
    (fun i h => by obtain ⟨_, ds, rfl, _⟩ := h; rfl)
    k i (by simpa [cleanBlock] using hi)
  rcases h with h | ⟨hk, hb, ha⟩
  · exact .inl h
  · exact .inr ⟨hb, hk, ha⟩

private theorem clean_entry {vc : VCode}
    (h0 : ∃ vb ds, vc.blocks[0]? = some vb ∧ vb.insts[0]? = some (.args ds)) :
    ∃ vb ds, (clean vc).blocks[0]? = some vb ∧ vb.insts[0]? = some (.args ds) := by
  obtain ⟨vb, ds, hb, hi⟩ := h0
  refine ⟨cleanBlock vc 0 vb, ds, ?_, ?_⟩
  · rw [clean_blocks_map, Array.getElem?_map, hb]; rfl
  · have hfirst : ∃ tail, vb.insts.toList = .args ds :: tail := by
      cases he : vb.insts.toList with
      | nil => simpa [← Array.getElem?_toList, he] using hi
      | cons a tail =>
        have ha : a = .args ds := by simpa [← Array.getElem?_toList, he] using hi
        exact ⟨tail, by rw [ha]⟩
    obtain ⟨tail, he⟩ := hfirst
    simp [cleanBlock, he, scan_head vc.classes.size (.args ds) tail (exitLive vc 0 vb) rfl]

/-- The old control-layout conditions hold after cleanup and preparation. -/
theorem ctlInsts_cleanup_pipeline {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode}
    (hsub : InSubset p f) (hd : Dominated f) (hs : LowerScope f)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare (prune vc) = .ok vcp) :
    (∀ b vb k i, vcp.blocks[b]? = some vb → vb.insts[k]? = some i →
      ctlInstOk b k i = true) ∧
    ∃ vb ds, vcp.blocks[0]? = some vb ∧ vb.insts[0]? = some (.args ds) ∧ 1 < vb.insts.size := by
  obtain ⟨hv, h0⟩ := vc_ctl hd hs (abiSigsOk_of_inSubset hsub) hl
  have hdom := prune_prepDomain (prepDomain_of_lower hs hl hs.nonempty)
  have hpv : ∀ b vb k i, (prune vc).blocks[b]? = some vb → vb.insts[k]? = some i →
      CtlNA i ∨ (b = 0 ∧ k = 0 ∧ ArgsOk i) := by
    unfold prune
    cases vc.cfg with
    | error e => exact hv
    | ok p => exact clean_ctl hv
  have hp0 : ∃ vb ds, (prune vc).blocks[0]? = some vb ∧ vb.insts[0]? = some (.args ds) := by
    unfold prune
    cases vc.cfg with
    | error e => exact h0
    | ok p => exact clean_entry h0
  refine ⟨fun b vb k i hb hi => ?_, prep_entry hp hdom hp0⟩
  rcases prep_ctl hp hdom hpv b vb k i hb hi with h | ⟨rfl, rfl, ds, rfl, ha⟩
  · exact h.2 b k
  · simpa [ctlInstOk] using ha

end E2E
