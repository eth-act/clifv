module

public import FV.Concurrency.VCodeSize
public import FV.Concurrency.VCodeFrameWitness

@[expose] public section

/-!
# Non-vacuity of `VCodeSize` (T2h, #311)

* `ldar_oneAcc`: `cEvs_size` on the `ldar` of `VCodeThread.Witness` (8 bytes, `csem F8` steps):
  its events have one address and 8 bytes;
* `ldar_at`: `addr_eq_of_oneAcc` on it: its events cover `[0x8000, 0x8008)`, so each is at
  `0x8000`.
-/

namespace Concurrency.VCodeSize.Witness

open Arm ArmThread Backend Backend.Proof VCodeThread VCodeThread.Witness VCodeAddr
  VCodeAddr.Witness

/-- **Non-vacuity of `cEvs_size`**: the `ldar`'s events are one access of 8 bytes. -/
theorem ldar_oneAcc : OneAcc 8 (cEvs F8 ctx0 iLdar [ofX 0x8000#64] w0) := by
  obtain ⟨r, hr⟩ := csem_ldar8
  exact cEvs_size (by decide +kernel)
    (fun _ => ⟨by decide +kernel, by unfold Arm.CheckSPAlignment; decide +kernel⟩) hr rfl

/-- **Non-vacuity of `addr_eq_of_oneAcc`**: the `ldar`'s events, covering the 8 bytes at
`0x8000`, are at `0x8000`. -/
theorem ldar_at : AtA (BitVec.ofNat 64 0x8000) 8 (cEvs F8 ctx0 iLdar [ofX 0x8000#64] w0) :=
  addr_eq_of_oneAcc (by decide) (by decide) (by decide) ldar_oneAcc (by decide +kernel)

end Concurrency.VCodeSize.Witness
