import FV.Backend.Proof.DeadCleanupFlow

namespace Backend.DeadCleanup

/-- The live-out set is uniform, so block indices do not affect cleaning. -/
theorem clean_blocks_map (vc : VCode) :
    (clean vc).blocks = vc.blocks.map (cleanBlock vc 0) := by
  apply Array.ext
  · simp [clean]
  · intro i h h'
    simp [clean, cleanBlock, exitLive]

theorem clean_block {vc : VCode} {b : Nat} {vb : VBlock}
    (h : vc.blocks[b]? = some vb) :
    (clean vc).blocks[b]? = some (cleanBlock vc 0 vb) := by
  simp [clean_blocks_map, h]

private theorem mapM_congr_mem {α β : Type} {f g : α → Except String β}
    (xs : List α) (h : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, List.mapM_cons, h x (by simp),
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- Cleaning preserves the entire CFG result for terminated blocks. -/
theorem clean_cfg (vc : VCode)
    (ht : ∀ b ∈ vc.blocks.toList, ∃ t, b.insts.back? = some t ∧ t.isTerminator = true) :
    (clean vc).cfg = vc.cfg := by
  unfold VCode.cfg
  simp only [clean_blocks_map, Array.size_map, Array.findIdx?_map,
    Function.comp_def, cleanBlock]
  congr 1
  rw [Array.mapM_map]
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList]
  congr 1
  apply mapM_congr_mem
  intro b hb
  obtain ⟨t, hback, hterm⟩ := ht b hb
  have hclean := cleanBlock_back vc 0 b hback hterm
  simp only [cleanBlock] at hclean
  simp [cleanBlock, hclean, hback]

example : ∃ vc : VCode,
    (∀ b ∈ vc.blocks.toList, ∃ t, b.insts.back? = some t ∧ t.isTerminator = true) ∧
    (clean vc).cfg = vc.cfg := by
  let vc : VCode := ⟨"cleanup_cfg", #[⟨0, #[deadMvn, liveBic, liveReturn], #[], #[]⟩],
    #[.int, .int, .int, .int], 0, 0, #[]⟩
  have ht : ∀ b ∈ vc.blocks.toList, ∃ t,
      b.insts.back? = some t ∧ t.isTerminator = true := by
    intro b hb
    simp only [vc, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst b
    exact ⟨liveReturn, rfl, rfl⟩
  exact ⟨vc, ht, clean_cfg vc ht⟩

end Backend.DeadCleanup
