import FV.E2E.LinkArmTwinC
import FV.E2E.LinkArmBlrCheck
import FV.E2E.LinkSlotSysWitness

/-!
# Witnesses for the `blr` check and the call-restricted twins on `Lsl` (SEM1 #537)

* `lsl_blrLow`: every compiled function of the slot system `Lsl` passes `FnAsm.blrLow`;
* `blr_x30_rejected`, `blr_x29_rejected`, `blr_x0_ok`: the line check rejects `blr x30`/`blr x29`
  and accepts `blr x0`;
* `twinC_Lsl`, `twinNC_Lsl`, `twinC_symm_Lsl`: the relations on `r`'s machine at every depth.
-/

namespace E2E.LinkSlotSysWitness

open Backend Backend.Proof

theorem lsl_blrLow : Lsl.P.funcs.all (fun g => (Lsl.A g).fa.blrLow) = true := by native_decide

theorem blr_x30_rejected : (Insn.blr (.x 30)).blrLow = false := by decide
theorem blr_x29_rejected : (Insn.blr (.x 29)).blrLow = false := by decide
theorem blr_x0_ok : (Insn.blr (.x 0)).blrLow = true := by decide

theorem twinC_Lsl (M : Nat) (s : Arm.ArmState) : Lsl.TwinC M fR s s := Lsl.twinC_refl M fR s

theorem twinNC_Lsl (M n : Nat) (s : Arm.ArmState) : Lsl.TwinNC M fR s s n :=
  Lsl.twinNC_refl M fR s n

theorem twinC_symm_Lsl (M : Nat) (s : Arm.ArmState) : Lsl.TwinC M fR s s :=
  LinkSys.TwinC.symm Lsl (twinC_Lsl M s)

end E2E.LinkSlotSysWitness
