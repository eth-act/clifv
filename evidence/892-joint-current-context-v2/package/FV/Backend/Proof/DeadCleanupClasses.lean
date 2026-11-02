import FV.Backend.Proof.DeadCleanupPrepare
import FV.Backend.Proof.SpillClasses

namespace Backend.DeadCleanup
open Backend.Proof Backend.Proof.Spill

/-- Retained instructions use the unchanged class array; edge interfaces remain
unchanged as well. -/
theorem clean_classes {vc : VCode} (h : ClassesOkM vc) : ClassesOkM (clean vc) := by
  refine ⟨?_, ?_⟩
  · simpa [clean] using clean_insts h.1
  · intro vb hb r hr
    simp only [clean_blocks_map, Array.toList_map, List.mem_map] at hb
    obtain ⟨vb0, hb0, rfl⟩ := hb
    exact h.2 vb0 hb0 r hr

theorem prune_classes {vc : VCode} (h : ClassesOkM vc) : ClassesOkM (prune vc) := by
  unfold prune
  cases vc.cfg with
  | error e => exact h
  | ok p => exact clean_classes h

end Backend.DeadCleanup
