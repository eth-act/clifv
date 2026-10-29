module

public import FV.Concurrency.CEvsInv
public import FV.Concurrency.VCodeFrameWitness

@[expose] public section

/-!
# Non-vacuity of the footprint invariances (T2h, #311, layer 2e)

On the `ldar` of `VCodeThread.Witness` (8 bytes at `0x8000`, frame `VCodeAddr.Witness.F8`):

* `ldar_atA_w0`: its one event on `w0` is at `0x8000` with 8 bytes;
* `ldar_atA_w5`: by `cEvs_setMem_atA`, so is every event on the patched world `w5` (the
  environment's `5` at `0x8000`);
* `ldar_renamed_atA`: by `cEvs_mapRegs`, so is every event of the `ldar` with renamed vregs
  (`g10`: vreg `n` ↦ vreg `n + 10`).
-/

namespace Concurrency.CEvsInv.Witness

open Arm ArmFoot ArmThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  VCodeThread.Witness VCodeAddr VCodeAddr.Witness

theorem ldar_atA_w0 : AtA 0x8000#64 8 (cEvs F8 ctx0 iLdar [ofX 0x8000#64] w0) := by
  unfold AtA; decide +kernel

theorem ldar_ne : cEvs F8 ctx0 iLdar [ofX 0x8000#64] w0 ≠ [] := by
  intro h
  have := ldar_evs_ne
  rw [h] at this
  cases this

/-- **`cEvs_setMem_atA` on a concrete step**: the `ldar`'s events on the patched world `w5` are
at `0x8000` with 8 bytes. -/
theorem ldar_atA_w5 : AtA 0x8000#64 8 (cEvs F8 ctx0 iLdar [ofX 0x8000#64] w5) := by
  obtain ⟨r, hr⟩ := csem_ldar8
  exact cEvs_setMem_atA (n := 8) (by decide +kernel)
    (fun _ => ⟨by decide +kernel, by unfold Arm.CheckSPAlignment; decide +kernel⟩) hr rfl
    (applyR [ev5] w0.mem) ldar_ne ldar_atA_w0

/-- Rename vreg `n` to vreg `n + 10`. -/
def g10 : Reg → Reg
  | .vreg n c => .vreg (n + 10) c
  | r => r

theorem g10_ren : VRenaming g10 (· + 10) where
  vreg _ _ := rfl
  real r h := by
    cases r with
    | vreg n c => exact absurd rfl (h n c)
    | _ => rfl

/-- **`cEvs_mapRegs` on a concrete instruction**: the renamed `ldar`'s events are the `ldar`'s. -/
theorem ldar_renamed_atA :
    AtA 0x8000#64 8 (cEvs F8 ctx0 (iLdar.mapRegs g10) [ofX 0x8000#64] w0) := by
  rw [cEvs_mapRegs g10_ren]
  exact ldar_atA_w0

end Concurrency.CEvsInv.Witness
