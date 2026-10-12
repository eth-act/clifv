import FV.Backend.Proof.DeadCleanupPrepare
import FV.Backend.Proof.SpillEdges

namespace Backend.DeadCleanup
open Backend.Proof Backend.Proof.Spill

private theorem clean_lookup {vc : VCode} {b : Nat} {vb : VBlock}
    (hb : (clean vc).blocks[b]? = some vb) :
    ∃ old, vc.blocks[b]? = some old ∧ vb = cleanBlock vc 0 old := by
  rw [clean_blocks_map, Array.getElem?_map] at hb
  obtain ⟨old, ho, he⟩ := Option.map_eq_some_iff.mp hb
  exact ⟨old, ho, he.symm⟩

private theorem clean_back {vc : VCode} {ss ps : Array (Array Nat)}
    (hc : vc.cfg = .ok (ss, ps)) {b : Nat} {vb : VBlock}
    (hb : vc.blocks[b]? = some vb) :
    (cleanBlock vc 0 vb).insts.back? = vb.insts.back? := by
  obtain ⟨t, _, ht, hterm, _⟩ := (Prep.cfg_spec hc).blk b vb hb
  exact (cleanBlock_back vc 0 vb ht hterm).trans ht.symm

/-- Cleanup preserves the existing lowering CFG and edge-interface invariant. -/
theorem clean_lowOk {vc : VCode} {ss ps : Array (Array Nat)}
    (hc : vc.cfg = .ok (ss, ps)) (hv : LowOk vc) : LowOk (clean vc) := by
  refine ⟨by simpa [clean] using hv.nonempty, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b vb hb
    obtain ⟨old, hb0, rfl⟩ := clean_lookup hb
    exact hv.labels b old hb0
  · intro vb hb
    obtain ⟨old, hb0, rfl⟩ := clean_lookup hb
    exact hv.entry old hb0
  · intro b vb t hb ht
    obtain ⟨old, hb0, rfl⟩ := clean_lookup hb
    rw [clean_back hc hb0] at ht
    exact hv.noEntry b old t hb0 ht
  · intro b vb hb hne
    obtain ⟨old, hb0, rfl⟩ := clean_lookup hb
    obtain ⟨l, tb, ht, htb, hsz, harg, hn⟩ := hv.args b old hb0 hne
    refine ⟨l, cleanBlock vc 0 tb, ?_, ?_, hsz, harg, hn⟩
    · rw [clean_back hc hb0]; exact ht
    · rw [clean_blocks_map, Array.getElem?_map, htb]; rfl
  · intro b vb t l tb hb hargs ht hl htb
    obtain ⟨old, hb0, rfl⟩ := clean_lookup hb
    obtain ⟨oldtb, htb0, rfl⟩ := clean_lookup htb
    rw [clean_back hc hb0] at ht
    exact hv.noArgs b old t l oldtb hb0 hargs ht hl htb0
  · intro b vb info ti hb ht
    obtain ⟨old, hb0, rfl⟩ := clean_lookup hb
    rw [clean_back hc hb0] at ht
    exact hv.tryArgs b old info ti hb0 ht
  · intro b vb info ti j l hb ht hl b' vb' t' j' hb' ht' hl'
    obtain ⟨old, hb0, rfl⟩ := clean_lookup hb
    obtain ⟨old', hb0', rfl⟩ := clean_lookup hb'
    rw [clean_back hc hb0] at ht
    rw [clean_back hc hb0'] at ht'
    exact hv.tryUniq b old info ti j l hb0 ht hl b' old' t' j' hb0' ht' hl'

theorem prune_lowOk {vc : VCode} (hv : LowOk vc) : LowOk (prune vc) := by
  unfold prune
  cases hc : vc.cfg with
  | error e => exact hv
  | ok p => exact clean_lowOk hc hv

end Backend.DeadCleanup
