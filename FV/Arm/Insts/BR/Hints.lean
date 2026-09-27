/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- NOP

import FV.Arm.Decode
import FV.Arm.Insts.Common

namespace Arm


----------------------------------------------------------------------

namespace BR

open _root_.BitVec Arm.BitVec

@[state_simp_rules]
def exec_hints (inst : Hints_cls) (s : ArmState) : ArmState :=
  if inst.CRm = 0b0000#4 ∧ inst.op2 = 0b000#3 then
    write_pc ((read_pc s) + 4#64) s
  else
    write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s

end BR

end Arm
