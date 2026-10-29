module

public import FV.E2E.LinkArmStepFrameRec
public import FV.E2E.ArmGprFootWitness

@[expose] public section

/-!
# Non-vacuity of the `x30` lock-step steps

`add_lockstep`: from any state and the same state with another `x30`, `add x0, x1, x2` gives
states equal but for `x30` (`stEqOutX_exec_inst`; it reads no memory). `add_lockstep_x0`: the
two results agree on `x0`, which the step wrote. `stp_lockstep`, `ldp_lockstep`,
`ret_lockstep_x0`: the frame-record pair and `ret` (`LinkArmStepFrameRec`).
-/

namespace E2E.GprFoot

open Arm

theorem add_lockstep (v : BitVec 64) (s : ArmState) :
    StEqOutX (fun _ => False) (exec_inst addX0X1X2 (setGpr 30#5 v s)) (exec_inst addX0X1X2 s) :=
  stEqOutX_exec_inst addX0X1X2 (by simp [addX0X1X2, Arm.ArmInst.gprs])
    (stEqOutX_setGpr30 v s) (fun _ _ _ _ _ h => h)

theorem add_lockstep_x0 (v : BitVec 64) (s : ArmState) :
    r (.GPR 0#5) (exec_inst addX0X1X2 (setGpr 30#5 v s)) = r (.GPR 0#5) (exec_inst addX0X1X2 s) :=
  (add_lockstep v s).1 _ (by simp)

/-- The prologue's frame-record store from two states that differ only in `x30`: they then
differ only in `x30` and the record's high 8 bytes (`stEqOutX_stpFR`). -/
theorem stp_lockstep (imm7 : BitVec 7) (v : BitVec 64) (s : ArmState) :
    StEqOutX (fun a => False ∨ HiBytes (stpAddr imm7 s) 8 16 a)
      (exec_inst (stpFR imm7) (setGpr 30#5 v s)) (exec_inst (stpFR imm7) s) :=
  stEqOutX_stpFR imm7 (stEqOutX_setGpr30 v s)

/-- The epilogue's frame-record load from two states that differ only in `x30`: `x29` is reloaded
from equal bytes (`stEqOutX_ldpFR`). -/
theorem ldp_lockstep (imm7 : BitVec 7) (v : BitVec 64) (s : ArmState) :
    StEqOutX (fun _ => False) (exec_inst (ldpFR imm7) (setGpr 30#5 v s))
      (exec_inst (ldpFR imm7) s) :=
  stEqOutX_ldpFR imm7 (stEqOutX_setGpr30 v s) fun _ _ h => h

/-- `ret` from two states that differ only in `x30`: they agree on every other register but the
pc (`stEqOutX_ret`). -/
theorem ret_lockstep_x0 (v : BitVec 64) (s : ArmState) :
    r (.GPR 0#5) (exec_inst retI (setGpr 30#5 v s)) = r (.GPR 0#5) (exec_inst retI s) :=
  (stEqOutX_ret (Z := fun _ => False) (stEqOutX_setGpr30 v s)).1 _ (by simp) (by simp)

/-- The backend's prologue frame-record store (`Asm`'s `stp fp, lr, [sp, #-16]!`) is `stpFR`. -/
theorem prologue_stp (env : Backend.Env) :
    (Backend.Insn.stp Backend.Reg.fp Backend.Reg.lr (.spPreIndexed (-16))).toArmInst env =
      .ok (stpFR 0x7e) := rfl

/-- The backend's epilogue frame-record load (`ldp fp, lr, [sp], #16`) is `ldpFR`. -/
theorem epilogue_ldp (env : Backend.Env) :
    (Backend.Insn.ldp Backend.Reg.fp Backend.Reg.lr (.spPostIndexed 16)).toArmInst env =
      .ok (ldpFR 2) := rfl

/-- The backend's `ret` is `retI`. -/
theorem ret_insn (env : Backend.Env) : Backend.Insn.ret.toArmInst env = .ok retI := rfl

end E2E.GprFoot
