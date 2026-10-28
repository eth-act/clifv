import FV.Backend.Proof.SpillLocal
import FV.Backend.Proof.RegallocOperands
import FV.Backend.Proof.LowerDecide
import FV.E2E.EmitCondsLower
import FV.Backend.Proof.IselEmitDriver
import FV.Backend.Proof.DeadCleanupPrepare
import FV.Backend.Proof.DeadCleanupPositions
import FV.Backend.Proof.CleanupStageFacts

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

private theorem clean_emit {vc : VCode}
    (h : ∀ vb ∈ vc.blocks.toList, (∀ i ∈ vb.insts.toList, i.emitOk = true) ∧ TargetsLast vb) :
    ∀ vb ∈ (clean vc).blocks.toList, (∀ i ∈ vb.insts.toList, i.emitOk = true) ∧ TargetsLast vb := by
  intro vb hb
  simp only [clean_blocks_map, Array.toList_map, List.mem_map] at hb
  obtain ⟨old, hb, rfl⟩ := hb
  refine ⟨fun i hi => (h old hb).1 i (cleanBlock_inst_mem vc 0 old i hi), ?_⟩
  intro i hi
  apply (h old hb).2 i
  exact (dropLast_sublist_of (scan_sublist vc.classes.size (exitDead vc old.label)
    old.insts.toList (exitLive vc 0 old))).subset
    (by simpa [cleanBlock] using hi)

private theorem prune_emit {vc : VCode}
    (h : ∀ vb ∈ vc.blocks.toList, (∀ i ∈ vb.insts.toList, i.emitOk = true) ∧ TargetsLast vb) :
    ∀ vb ∈ (prune vc).blocks.toList, (∀ i ∈ vb.insts.toList, i.emitOk = true) ∧ TargetsLast vb := by
  unfold prune
  cases vc.cfg with
  | error e => exact h
  | ok p => exact clean_emit h

/-- The skip keeps the last instruction of a block and deletes others, so it keeps the facts. -/
private theorem skipBlock_emit (mask : Nat → List Bool) {vb : VBlock}
    (h : (∀ i ∈ vb.insts.toList, i.emitOk = true) ∧ TargetsLast vb) :
    (∀ i ∈ (skipBlock mask vb).insts.toList, i.emitOk = true) ∧ TargetsLast (skipBlock mask vb) := by
  unfold skipBlock
  split
  · rename_i hf
    obtain ⟨m', ms', x, hm, hx, hl⟩ := maskFits_split hf
    have hk : maskKeep (mask vb.label) vb.insts.toList = maskKeep m' ms' ++ [x] := by
      rw [hm, hx, maskKeep_append_last _ _ _ hl]
    have hs := maskKeep_sublist m' ms'
    refine ⟨fun i hi => h.1 i ?_, fun i hi => h.2 i ?_⟩
    · simp only [List.toList_toArray, hk] at hi
      rw [hx]
      rcases List.mem_append.mp hi with hi | hi
      · exact List.mem_append_left _ (hs.subset hi)
      · exact List.mem_append_right _ hi
    · simp only [List.toList_toArray, hk, List.dropLast_concat] at hi
      rw [hx, List.dropLast_concat]
      exact hs.subset hi
  · exact h

private theorem skipStage_emit (f : Clif.Function) {vc : VCode}
    (h : ∀ vb ∈ vc.blocks.toList, (∀ i ∈ vb.insts.toList, i.emitOk = true) ∧ TargetsLast vb) :
    ∀ vb ∈ (skipStage f vc).blocks.toList,
      (∀ i ∈ vb.insts.toList, i.emitOk = true) ∧ TargetsLast vb := by
  intro vb hb
  rw [skipStage_eq, mapBlocks_blocks, Array.toList_map, List.mem_map] at hb
  obtain ⟨old, hb, rfl⟩ := hb
  exact skipBlock_emit _ (h old hb)

/-- Immediate, condition-code and label facts need no new source conditions. (`hp` is about the
production cleanup stage `cleanupStage f vc`, formerly `prune vc`.) -/
theorem emitConds_cleanup_lower {f : Clif.Function} {vc vcp : VCode} (hs : LowerScope f)
    (hI : IselEmit f) (hl : lowerFunction f = .ok vc)
    (hp : Backend.prepare (cleanupStage f vc) = .ok vcp) :
    immsOkB vcp = true ∧ vcp.noAlwaysB = true ∧ branchTargetsOkB vcp = true := by
  have hd := cleanupStage_prepDomain f (prepDomain_of_lower hs hl hs.nonempty)
  have hv := prep_emit hp hd (prune_emit (skipStage_emit f (vc_emit hI hs.subsetE hl)))
  have hok : ∀ vb ∈ vcp.blocks.toList, ∀ m ∈ vb.insts.toList,
      immOkB m = true ∧ m.noAlways = true := fun vb hvb m hm => by
    have := (hv vb hvb).1 m hm
    simpa [MInst.emitOk] using this
  refine ⟨?_, ?_, branchTargetsOk_of hp hd (fun vb h => (hv vb h).2)⟩
  · unfold immsOkB
    rw [Array.all_eq_true_iff_forall_mem]
    intro vb hvb
    rw [Array.all_eq_true_iff_forall_mem]
    intro m hm
    exact (hok vb (Array.mem_toList_iff.mpr hvb) m (Array.mem_toList_iff.mpr hm)).1
  · unfold VCode.noAlwaysB
    rw [List.all_eq_true]
    intro vb hvb
    rw [List.all_eq_true]
    intro m hm
    exact (hok vb hvb m hm).2

/-- The old size and widening conditions still suffice for emission. -/
theorem emitCondsB_cleanup_of_input {f : Clif.Function} {vc vcp : VCode}
    (hs : lowerScopeB f = true) (hw : extendsWidenB f = true)
    (hl : lowerFunction f = .ok vc) (hp : Backend.prepare (cleanupStage f vc) = .ok vcp)
    (hsz : spillSizeOkB vcp = true) : emitCondsB vcp = true := by
  obtain ⟨h1, h2, h3⟩ := emitConds_cleanup_lower (lowerScope_of hs)
    (iselEmit (lowerScope_of hs) hw) hl hp
  simp [emitCondsB, hsz, h1, h2, h3]

end E2E
