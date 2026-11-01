import FV.E2E.DeadCleanupLinkCheck
import FV.Backend.Proof.IselOutBoundRun

/-!
# The outgoing bound from the input (S10g, #404)

The input condition `outBoundB` on the call signatures bounds the compiled code's outgoing
area (`Backend.Proof.OutBound.lowerFunction_outgoing_le`); `prune` and `prepare` keep it:
**`vcp_outgoing_le`**. (#514's frame layout needed this bound for `saveFrameB`; the stock
Cranelift frame of #549 makes the saves' rows independent of it.)
-/

namespace Link.EhCheck.Complete

set_option autoImplicit false

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.OutBound E2E E2E.LinkCheck

/-- **The prepared VCode's outgoing area is at most 32560 bytes** on `LowerScope` input with
`outBoundB`: `lowerFunction_outgoing_le`, and `prune` and `prepare` keep the outgoing area. -/
theorem vcp_outgoing_le {g : Clif.Function} {k : Nat} {base : BitVec 64} {o : Lean.Json} {a : Art}
    (hpipe : pipeCleanupT g k base o = .ok a) (hs : LowerScope g) (hob : outBoundB g = true) :
    a.vcp.outgoing ≤ 32560 := by
  obtain ⟨hl, hp, -⟩ := pipeCleanupT_spec hpipe
  rw [Prep.prepare_outgoing hp (cleanupStage_prepDomain g (Driver.prepDomain_of hs hl)),
    cleanupStage_outgoing]
  exact lowerFunction_outgoing_le hs hob hl

end Link.EhCheck.Complete
