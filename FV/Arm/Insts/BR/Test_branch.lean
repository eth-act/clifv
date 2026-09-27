/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license as described in third_party/lnsym-upstream/LICENSE.
-/
-- (FV addition, not in LNSym) TBZ, TBNZ.
--
-- Transcribed from the Arm ARM (DDI 0487) "TBZ" / "TBNZ" ASL:
--
--   integer t = UInt(Rt);
--   constant integer datasize = 64 << UInt(b5);   // 32 when b5 = 0, the W form
--   integer bit_pos = UInt(b5:b40);
--   bit op = op;                                   // 0 = TBZ, 1 = TBNZ
--   bits(64) offset = SignExtend(imm14:'00', 64);
--
--   bits(datasize) operand = X[t, datasize];
--   if operand<bit_pos> == op then
--       BranchTo(PC[] + offset, BranchType_DIR, FALSE);
--   else
--       BranchNotTaken(BranchType_DIR, FALSE);
--
-- Register 31 is XZR. Only bit `bit_pos` is read, so `datasize` does not affect the result.

import FV.Arm.Decode
import FV.Arm.Insts.Common

namespace Arm

namespace BR

open _root_.BitVec Arm.BitVec

@[state_simp_rules]
def Test_branch_inst.branch_taken_pc (inst : Test_branch_cls) (pc : BitVec 64) : BitVec 64 :=
  pc + signExtend 64 (inst.imm14 ++ 0b00#2)

@[state_simp_rules]
def Test_branch_inst.condition_holds (inst : Test_branch_cls) (s : ArmState) : Bool :=
  let bit_pos := (inst.b5 ++ inst.b40).toNat
  let operand := read_gpr_zr 64 inst.Rt s
  lsb operand bit_pos = inst.op

@[state_simp_rules]
def exec_test_branch (inst : Test_branch_cls) (s : ArmState) : ArmState :=
  let orig_pc := read_pc s
  let next_pc :=
    if Test_branch_inst.condition_holds inst s then
      Test_branch_inst.branch_taken_pc inst orig_pc
    else
      orig_pc + 4#64
  write_pc next_pc s

end BR

end Arm
