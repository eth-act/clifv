import FV.Concurrency.VCodeFrame
import FV.Concurrency.VCodeThreadWitness

/-!
# Non-vacuity of `VCodeAddr.cEvs_avoid` (T2h, #311, layer 2a)

`ldar_avoid`: the `ldar` of `VCodeThread.Witness` (8 bytes at `0x8000`) under the frame set `F8`
of every address outside `[0x8000, 0x8008)` (the bytes of the CLIF event it realizes): `csem F8`
steps, so by `cEvs_avoid` its one event (`ldar_evs_ne`: it has one) lies in those bytes.
-/

namespace Concurrency.VCodeAddr.Witness

open Arm ArmThread Backend Backend.Proof VCodeThread VCodeThread.Witness

/-- Every address outside the 8 bytes at `0x8000`. -/
def F8 (a : BitVec 64) : Prop := ¬ (0x8000#64 ≤ a ∧ a < 0x8008#64)

instance : DecidablePred F8 := fun a => by unfold F8; infer_instance

theorem accessOk_ldar :
    AccessOk F8 ctx0 ic0 (placeUses ops0 (canonRegs ops0) [ofX 0x8000#64] w0) := by
  unfold AccessOk Avoids
  decide +kernel

theorem exec_t0 : ∃ t, execMInst ctx0 env0 ic0 (placeUses ops0 (canonRegs ops0) [ofX 0x8000#64] w0) =
    some t ∧ Arm.r .ERR t = .None ∧ t.program = w0.program := by
  have h : (execMInst ctx0 env0 ic0 (placeUses ops0 (canonRegs ops0) [ofX 0x8000#64] w0)).isSome := by
    decide +kernel
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
  have he : (Arm.r .ERR t == .None) = true := by
    have : ((execMInst ctx0 env0 ic0 (placeUses ops0 (canonRegs ops0) [ofX 0x8000#64] w0)).map
      fun t => Arm.r .ERR t == .None) = some true := by decide +kernel
    rw [ht] at this; simpa using this
  have hp : @BEq.beq (List (BitVec 64 × BitVec 32)) _ t.program w0.program = true := by
    have : ((execMInst ctx0 env0 ic0 (placeUses ops0 (canonRegs ops0) [ofX 0x8000#64] w0)).map
      fun t => @BEq.beq (List (BitVec 64 × BitVec 32)) _ t.program w0.program) = some true := by
      decide +kernel
    rw [ht] at this; simpa using this
  exact ⟨t, ht, by simpa using he, @eq_of_beq (List (BitVec 64 × BitVec 32)) _ _ _ _ hp⟩

/-- `csem F8` steps on the `ldar`. -/
theorem csem_ldar8 : ∃ r, csem F8 ctx0 X0 iLdar [ofX 0x8000#64] w0 = some r := by
  obtain ⟨t, ht, he, hp⟩ := exec_t0
  rw [csem_of_wf (by decide) (by decide +kernel) (by decide +kernel)
    (by unfold Arm.CheckSPAlignment; decide +kernel)]
  exact ⟨_, straightSem_eq ops0_eq ic0_eq accessOk_ldar ht he hp⟩

/-- The `ldar` has one event. -/
theorem ldar_evs_ne : (cEvs F8 ctx0 iLdar [ofX 0x8000#64] w0).length = 1 := by
  decide +kernel

/-- **Non-vacuity of `cEvs_avoid`**: the `ldar`'s event avoids `F8`. -/
theorem ldar_avoid : EvsAvoid F8 (cEvs F8 ctx0 iLdar [ofX 0x8000#64] w0) := by
  obtain ⟨r, hr⟩ := csem_ldar8
  exact cEvs_avoid (by decide +kernel)
    (fun _ => ⟨by decide +kernel, by unfold Arm.CheckSPAlignment; decide +kernel⟩) hr

end Concurrency.VCodeAddr.Witness
