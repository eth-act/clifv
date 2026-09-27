/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
-- CSEL, CSINC, CSINV, CSNEG: 32- and 64-bit versions

import FV.Arm.Decode
import FV.Arm.State
import FV.Arm.Insts.Common
import FV.Arm.BitVec

namespace Arm


namespace DPR

open _root_.BitVec Arm.BitVec

@[state_simp_rules]
def exec_conditional_select (inst : Conditional_select_cls) (s : ArmState) : ArmState :=
    let datasize := if inst.sf = 1#1 then 64 else 32
    let (unimplemented, result) :=
      match inst.op, inst.S, inst.op2 with
        | 0b0#1, 0b0#1, 0b00#2 => -- CSEL
          (false,
            if ConditionHolds inst.cond s then
              read_gpr_zr datasize inst.Rn s
            else
              read_gpr_zr datasize inst.Rm s)
        | _, _, _ =>
          (true, BitVec.ofNat datasize 0)
    -- State Updates
    if unimplemented then
      write_err
        (StateError.Unimplemented
          s!"Unsupported DPR.Conditional_select_cls {inst} encountered in exec_inst!")
      s
    else
      let s            := write_pc ((read_pc s) + 4#64) s
      let s            := write_gpr_zr datasize inst.Rd result s
      s

----------------------------------------------------------------------

end DPR

end Arm
