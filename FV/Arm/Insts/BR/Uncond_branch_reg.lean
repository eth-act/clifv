/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/

-- RET, BR, BLR
-- Modified by fv-compiler-rust (2026): ported to Lean v4.34.1, module prefix FV.Arm, wrapped in
-- namespace Arm; BR and BLR added (upstream: RET only), and the target register 31 is XZR
-- (upstream read SP). Arm ARM (DDI 0487) "BR"/"BLR"/"RET" ASL:
--   bits(64) target = X[n, 64];
--   if branch_type == BranchType_INDCALL then X[30, 64] = PC[] + 4;   // BLR
--   BranchTo(target, branch_type, FALSE);
-- The target is read before X30 is written (so `blr x30` branches to the old X30).
-- Model assumption: no top-byte-ignore (`AArch64.BranchAddr` with `AddrTop = 63`); Cranelift
-- never branches to tagged addresses.

import FV.Arm.Decode
import FV.Arm.State
import FV.Arm.Insts.Common
import FV.Arm.BitVec

namespace Arm


namespace BR

open _root_.BitVec Arm.BitVec

@[state_simp_rules]
def exec_uncond_branch_reg (inst : Uncond_branch_reg_cls) (s : ArmState) : ArmState :=
    -- Only BR (opc = 0000), BLR (0001) and RET (0010) without pointer authentication.
    if not ((inst.opc = 0b0000#4 ∨ inst.opc = 0b0001#4 ∨ inst.opc = 0b0010#4) ∧
            inst.op2 = 0b11111#5 ∧ inst.op3 = 0b000000#6 ∧ inst.op4 = 0b00000#5) then
       write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s
    else
      let target := read_gpr_zr 64 inst.Rn s
      -- State Updates
      let s := if inst.opc = 0b0001#4 then write_gpr 64 30#5 ((read_pc s) + 4#64) s else s
      let s := write_pc target s
      s

end BR

end Arm
