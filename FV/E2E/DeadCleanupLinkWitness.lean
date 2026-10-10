import FV.E2E.DeadCleanupLinkCheck
import FV.E2E.DeadCleanupLinkFrames
import FV.E2E.DeadCleanupWitness

namespace E2E.DeadCleanupLinkWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup E2E.LinkCheck

/-- A nonempty source fixture with an unused constant; the same input is checked
by both pipelines. The failed oracle answer exercises the real spill fallback. -/
private def fixture : FnInput :=
  { clif := "function %cleanup_unused() {\nblock0:\n v0 = iconst.i64 17\n return\n}\n", ra := "{}" }

def input : LinkInput :=
  { funcs := [fixture], addrs := [("cleanup_unused", 65536)], syms := [], raStar := 8,
    D := 1024, fallback := true }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Fixed witness receipt, excluded from production correctness roots. -/
theorem checkers_accept : okB input = true ∧ okBCleanup input = true := by native_decide

/-- Frame and entry-register transports apply to an actual source compilation
which deletes an instruction and emits laid-out code. -/
theorem frame_entry_witness : ∃ vc raw vcp rf af fa fb,
    lowerFunction DeadCleanupWitness.source = .ok vc ∧
    Backend.prepare vc = .ok raw ∧ vcp = preparedCleanup vc raw ∧
    lowerRFunc vcp rf = .ok af ∧ emitFunc 0 af = .ok fa ∧ fa.layout = .ok fb ∧
    entryB DeadCleanupWitness.source vcp = true ∧
    ((!DeadCleanupWitness.source.slots.isEmpty || (RAFrame.compute vcp rf).size == af.frameSize) &&
      slotFitsB DeadCleanupWitness.source ⟨0, vc, vcp, rf, af, fa, fb, 0⟩) = true ∧
    (prune vc).blocks[0]!.insts.size < vc.blocks[0]!.insts.size := by
  obtain ⟨hd, hs, har, vc, vcp, af, fa, fb, hc, hshr⟩ := DeadCleanupWitness.compiled_exists
  obtain ⟨raw, hp, hv⟩ := prune_prepare_ok_inv hc.prepare
  refine ⟨vc, raw, vcp, spillAlloc vcp, af, fa, fb, hc.lower, hp, hv, hc.alloc,
    hc.emit, hc.layout, ?_, ?_, hshr⟩
  · rw [hv]
    exact entryB_cleanup_of_lower (by
      have h := DeadCleanupWitness.checks_true
      simp only [DeadCleanupWitness.checks, Bool.and_eq_true] at h
      exact h.1.1.1.2) hc.lower hp
  · exact frame_cleanup_of_lower
      (a := ⟨0, vc, vcp, spillAlloc vcp, af, fa, fb, 0⟩) hc.lower hp hv hc.alloc

end E2E.DeadCleanupLinkWitness
