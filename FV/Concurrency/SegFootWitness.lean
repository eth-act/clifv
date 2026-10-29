module

public import FV.Concurrency.SegFoot
public import FV.Concurrency.VCodeThreadWitness

@[expose] public section

/-!
# Non-vacuity of the footprint premises along a run (T2h, #311, layer 2e step 2)

* `keep_ldar`: `csem_keep` on the successful `ldar` step of `VCodeThread.Witness` (`csem_ldar`):
  the world after it is error-free, with the same (aligned) `sp`;
* `runFoot_ldar_fence`: `runFoot_csem` on the two-instruction segment `ldar; dmb ish` from the
  patched world `w5`;
* `fence_foot_after_ldar`: the segment's `RunFoot` gives the precise footprint of the `dmb` at
  the state the `ldar` step reaches (`t5`, the vreg file after the `ldar`'s def).
-/

namespace Concurrency.SegFoot.Witness

open Arm ArmFoot ArmThread Backend Backend.Proof VCodeThread VCodeThread.Witness IselCover

/-- **`csem_keep` on a concrete step**: after the `ldar`, no error and the same aligned `sp`. -/
theorem keep_ldar : Arm.r .ERR t5 = .None ∧ Arm.CheckSPAlignment t5 ∧
    Arm.r (.GPR 31#5) t5 = Arm.r (.GPR 31#5) w5 :=
  csem_keep (F := fun _ => False) (ctx := ctx0) (X := X0) (i := iLdar) (u := [ofX 0x8000#64])
    (w := w5) (fun _ h => nomatch h) (fun _ _ h => nomatch h) (.inr (by decide +kernel))
    (by decide +kernel) (by unfold Arm.CheckSPAlignment; decide +kernel) csem_ldar

/-- The segment: `ldar`, then `dmb ish`. -/
def seg : List MInst := [iLdar, .fence]

theorem seg_covered : ∀ i ∈ seg, Covered ctx0 i := by
  intro i hi
  simp only [seg, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h), .inr (by decide +kernel)⟩
  · exact ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h), .inr rfl⟩

/-- **`runFoot_csem` on a concrete segment.** -/
theorem runFoot_ldar_fence :
    RunFoot (csem (fun _ => False) ctx0 X0) (cEvs (fun _ => False) ctx0) seg ρ0 w5 :=
  runFoot_csem X0_tls seg_covered (by decide +kernel)
    (by unfold Arm.CheckSPAlignment; decide +kernel)

/-- The vreg file after the `ldar`. -/
def ρ1 : Nat → CV := vdefUpd ops0 (defVals ops0 (canonRegs ops0) t5) ρ0

/-- **The footprint at a reached state**: the segment's `RunFoot` gives the `dmb`'s precise
footprint at the world `t5` the `ldar` step reaches. -/
theorem fence_foot_after_ldar : ∀ ops, MInst.fence.operands = .ok ops →
    IFoot (csem (fun _ => False) ctx0 X0) .fence (vuses ops ρ1) t5
      (cEvs (fun _ => False) ctx0 .fence (vuses ops ρ1) t5) := by
  have hs : csem (fun _ => False) ctx0 X0 iLdar (vuses ops0 ρ0) w5 =
      some (defVals ops0 (canonRegs ops0) t5, t5, .next) := by
    have hu : vuses ops0 ρ0 = [ofX 0x8000#64] := uses0
    rw [hu]; exact csem_ldar
  have h2 := (runFoot_ldar_fence ops0 ops0_eq).2 _ _ hs
  intro ops hops
  exact (h2 ops hops).1

end Concurrency.SegFoot.Witness
