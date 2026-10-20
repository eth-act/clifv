import FV.Concurrency.ArmAllocSeg
import FV.Concurrency.ArmAllocThreadWitness

/-!
# Non-vacuity of the segment lemmas of layer 4b (T2h, #311)

`one_read_ldaxr`: `ArmAllocThread.prun_one_read` for the one-instruction segment at the
`ldaxr x27, [x25]` of `ArmThread.Witness` (its single-core step reads `0x8000`): the precise run
whose `ldaxr` reads the environment's `5` (its own memory holds `0`) is the single-core step from
the state patched with that read.
-/

namespace Concurrency.ArmAllocThread.Witness

open Arm ArmFoot ArmThread ArmInstFoot ArmPrecise VCodeThread Backend.Proof

/-- The `ldaxr`'s single-core read. -/
abbrev e0 : Ev := ⟨.acqXR, 0x8000#64, 8, readM 8 0x8000#64 st0.mem⟩

theorem noStx_st0 : NoStx st0 := fun _ _ _ h => by rw [cls_st0] at h; cases h

/-- **Non-vacuity of `prun_one_read`**: the run reading the environment's `5` is the single-core
step from the state patched with the read. -/
theorem one_read_ldaxr : ∃ t', PRun Policy.arm stepi (fun _ _ => True) (st0, none)
      [⟨[ArmThread.Witness.evRead], false⟩] t' ∧
    ∃ e, SameAcc e e0 ∧ t'.1 = iterN stepi 1 (patch [e] st0) ∧
      evTr [⟨[ArmThread.Witness.evRead], false⟩] = segEvs stepi 1 (patch [e] st0) := by
  obtain ⟨t', h1, h2⟩ := ThreadLayerWitness.precise_ldaxr
  have hr : PRun Policy.arm stepi (fun _ _ => True) (st0, none)
      [⟨[ArmThread.Witness.evRead], false⟩] t' := .cons h1 h2 trivial .nil
  refine ⟨t', hr, ?_⟩
  rcases prun_one_read (N := 1) (i0 := 0) (e0 := e0) rfl (by decide) Nat.one_pos
      (fun i hi => absurd hi (Nat.not_lt_zero _)) stepEvs_st0 noStx_st0
      (fun _ _ i h1 h2 => absurd h2 (by omega)) hr (by simp) with ⟨h, -⟩ | ⟨e, he, h1, h2, -⟩
  · simp at h
  · exact ⟨e, he, h1, h2⟩

end Concurrency.ArmAllocThread.Witness
