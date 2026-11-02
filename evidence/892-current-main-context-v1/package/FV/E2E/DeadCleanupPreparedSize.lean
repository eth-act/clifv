import FV.E2E.DeadCleanupSpillWords
import FV.Backend.Proof.DeadCleanupPrepareMap

namespace E2E
open Backend Backend.DeadCleanup
open Backend.Proof.Prep

/-- Cleanup transports the exact baseline spill bound through preparation. -/
theorem preparedCleanup_spillWordBound_le (vc vcp : VCode)
    {succs preds : Array (Array Nat)} (hc : vcp.cfg = .ok (succs, preds)) :
    spillWordBound (preparedCleanup vc vcp) ≤ spillWordBound vcp := by
  apply spillWordBound_map_mono vcp (preparedCleanup vc vcp) (preparedCleanupBlock vc)
    (preparedCleanup_blocks vc vcp)
  · exact fun b => (preparedCleanupBlock_interface vc b).2.2.1
  · exact fun b => (preparedCleanupBlock_interface vc b).2.1
  · exact fun b => (preparedCleanupBlock_interface vc b).2.2.2
  · exact preparedCleanupBlock_sublist vc
  · exact hc
  · rw [preparedCleanup_cfg]
    exact hc

/-- The old prepared-code size premise suffices; no stronger source premise is
introduced for the linked-program completeness theorem. -/
theorem preparedCleanup_spillSizeOkB (vc vcp : VCode)
    {succs preds : Array (Array Nat)} (hc : vcp.cfg = .ok (succs, preds))
    (hs : spillSizeOkB vcp = true) : spillSizeOkB (preparedCleanup vc vcp) = true := by
  have hm := preparedCleanup_spillWordBound_le vc vcp hc
  have hsize : spillWordBound vcp < 2 ^ 24 := of_decide_eq_true hs
  exact decide_eq_true (by omega)

/-! Joint non-vacuity: valid CFG, real deletion and the transported bound. -/
example : ∃ vc : VCode, (∃ ss ps, vc.cfg = .ok (ss, ps)) ∧
    (preparedCleanup vc vc).blocks[0]!.insts.toList = [liveBic, liveReturn] ∧
    spillWordBound (preparedCleanup vc vc) ≤ spillWordBound vc := by
  let vb : VBlock := ⟨0, #[deadMvn, liveBic, liveReturn], #[], #[]⟩
  let vc : VCode := ⟨"cleanup_size", #[vb], #[.int, .int, .int, .int], 0, 0, #[]⟩
  obtain ⟨ss, ps, hc⟩ : ∃ ss ps, vc.cfg = .ok (ss, ps) := cfg_of (by
    intro i b hi
    have hn := (Array.getElem?_eq_some_iff.mp hi).1
    have hz : i = 0 := by simp [vc] at hn; omega
    subst i
    have he : b = vb := (Option.some.inj (show some vb = some b by simpa [vc] using hi)).symm
    subst b
    exact ⟨liveReturn, rfl, rfl, fun l hl => by cases hl⟩)
  refine ⟨vc, ⟨ss, ps, hc⟩, ?_, preparedCleanup_spillWordBound_le vc vc hc⟩
  rw [preparedCleanup_blocks]
  simp only [vc, Array.map_singleton]
  simp only [getElem!_def, Array.getElem?_singleton, if_true]
  rw [preparedCleanupBlock_insts vc (show vb.insts.back? = some liveReturn from rfl) rfl]
  decide

end E2E
