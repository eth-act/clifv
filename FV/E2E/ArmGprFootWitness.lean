module

public import FV.E2E.ArmGprFoot

@[expose] public section

/-!
# Non-vacuity of the general-purpose register footprint

* `add_x30Free`: `add x0, x1, x2` neither reads nor writes `x30` (`gprFree_exec_inst`);
* `str_d30_x30Free`: `str d30, [sp, #8]` (a SIMD&FP store of `v30`) names no GPR `x30`;
* `ret_names_x30`, `bl_names_x30`, `stp_fp_lr_names_x30`: `ret`, `bl` and the frame-record store
  `stp x29, x30, [sp, #-16]!` name `x30` (the footprint does not exclude them);
* `add_writes_x0`: the footprint is not trivially true: `add x0, x1, x2` does not commute with
  setting `x0`.
-/

namespace E2E.GprFoot

open Arm

/-- `add x0, x1, x2`. -/
def addX0X1X2 : ArmInst :=
  .DPR (.Add_sub_shifted_reg
    { sf := 1, op := 0, S := 0, shift := 0, Rm := 2, imm6 := 0, Rn := 1, Rd := 0 })

theorem add_x30Free : GprFree 30#5 (exec_inst addX0X1X2) :=
  gprFree_exec_inst _ (by decide) (by simp [addX0X1X2, Arm.ArmInst.gprs])

/-- `str d30, [sp, #8]` (unsigned offset, SIMD&FP, 64-bit). -/
def strD30 : ArmInst :=
  .LDST (.Reg_unsigned_imm { size := 3, V := 1, opc := 0, imm12 := 1, Rn := 31, Rt := 30 })

theorem str_d30_x30Free : GprFree 30#5 (exec_inst strD30) :=
  gprFree_exec_inst _ (by decide) (by simp [strD30, Arm.ArmInst.gprs])

theorem ret_names_x30 :
    30#5 ∈ (ArmInst.BR (.Uncond_branch_reg { opc := 2, op2 := 31, op3 := 0, Rn := 30, op4 := 0 })).gprs := by
  decide

theorem bl_names_x30 : 30#5 ∈ (ArmInst.BR (.Uncond_branch_imm { op := 1, imm26 := 4 })).gprs := by
  decide

theorem stp_fp_lr_names_x30 :
    30#5 ∈ (ArmInst.LDST (.Reg_pair_pre_indexed
      { opc := 2, V := 0, L := 0, imm7 := 0x7e, Rt2 := 30, Rn := 31, Rt := 29 })).gprs := by
  decide

/-- The footprint is informative: `add x0, x1, x2` writes `x0`, so it does not commute with
setting `x0` (on the state where `x1 = x2 = 0`, i.e. `x0` becomes `0` either way, but setting
`x0 := 1` afterwards differs). -/
theorem add_writes_x0 : ¬ GprFree 0#5 (exec_inst addX0X1X2) := by
  intro h
  have := congrArg (fun s => r (.GPR 0#5) s) (h 1#64 ArmState.default)
  simp only [setGpr] at this
  revert this
  decide +kernel

end E2E.GprFoot
