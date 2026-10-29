module

public import FV.ArmFault.Step

@[expose] public section

/-!
# Non-vacuity of the Arm fault model (A3, #412, F1)

One instruction at `0x1000`, `ldr x0, [x1]` (`f9400020`) or `str x0, [x1]` (`f9000020`), and the
map `map`: the page `[0, 0x1000)` unmapped, `[0x2000, 0x3000)` read-only, the rest read-write.

* `ldr_null_faults`, `ldr_null_stepF`: the load from address 0 faults; the fault state is the
  state with the error `memFault` (`ldr_null_err`), while `stepi` loads (`ldr_null_stepi`);
* `ldr_straddle_faults`: a load from `0xffc` (its first 4 bytes unmapped) faults;
* `ldr_mapped`: a load from `0x8000` does not fault, `stepF` is `stepi`;
* `ldr_ro`, `str_ro_faults`, `str_straddle_ro_faults`: a read-only byte allows the load, not the
  store (also when only the last byte of the store is read-only).
-/

namespace ArmFault.Witness

open Arm

/-- `[0, 0x1000)` unmapped, `[0x2000, 0x3000)` read-only, the rest read-write. -/
def map : MemMap := fun a =>
  if a.toNat < 0x1000 then .none else if 0x2000 ≤ a.toNat ∧ a.toNat < 0x3000 then .ro else .rw

/-- `ldr x0, [x1]` -/
def ldrW : BitVec 32 := 0xf9400020#32
/-- `str x0, [x1]` -/
def strW : BitVec 32 := 0xf9000020#32

/-- The instruction `i` at `0x1000`, x1 = `x1`, x0 = 7. -/
def st (i : BitVec 32) (x1 : BitVec 64) : ArmState :=
  w .PC 0x1000#64 (w (.GPR 0#5) 7#64 (w (.GPR 1#5) x1
    (set_program ArmState.default [(0x1000#64, i)])))

theorem ldr_null_faults : Faults map (st ldrW 0#64) := by decide +kernel

theorem ldr_null_stepF : stepF map (st ldrW 0#64) = write_err memFault (st ldrW 0#64) :=
  stepF_fault ldr_null_faults

theorem ldr_null_err : r .ERR (stepF map (st ldrW 0#64)) = memFault :=
  err_stepF_fault ldr_null_faults

/-- The fault-free model loads from address 0 and goes on. -/
theorem ldr_null_stepi : r .ERR (stepi (st ldrW 0#64)) = .None ∧
    r .PC (stepi (st ldrW 0#64)) = 0x1004#64 := by decide +kernel

theorem ldr_straddle_faults : Faults map (st ldrW 0xffc#64) := by decide +kernel

theorem ldr_mapped_ok : ¬ Faults map (st ldrW 0x8000#64) := by decide +kernel

theorem ldr_mapped : stepF map (st ldrW 0x8000#64) = stepi (st ldrW 0x8000#64) :=
  stepF_of_not ldr_mapped_ok

theorem ldr_ro : ¬ Faults map (st ldrW 0x2000#64) := by decide +kernel

theorem str_ro_faults : Faults map (st strW 0x2000#64) := by decide +kernel

theorem str_straddle_ro_faults : Faults map (st strW 0x1ff9#64) := by decide +kernel

theorem str_rw_ok : ¬ Faults map (st strW 0x8000#64) := by decide +kernel

end ArmFault.Witness
