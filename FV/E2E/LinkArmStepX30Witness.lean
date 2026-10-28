import FV.E2E.LinkArmStepX30
import FV.E2E.ArmGprFootWitness

/-!
# Non-vacuity of the `x30` lock-step step

`add_lockstep`: from any state and the same state with another `x30`, `add x0, x1, x2` gives
states equal but for `x30` (`stEqOutX_exec_inst`; it reads no memory). `add_lockstep_x0`: the
two results agree on `x0`, which the step wrote.
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

end E2E.GprFoot
