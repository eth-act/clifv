/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license; see third_party/NOTICE-lnsym.md.
-/
-- (FV addition, not in LNSym) Floating-point conditional select: FCSEL, single (`ftype = 00`)
-- and double (`ftype = 01`) precision.
--
-- Transcribed from the Arm ARM (DDI 0487) "FCSEL" ASL:
--
--   if ftype == '10' then UNDEFINED;                          // (M, S nonzero: unallocated)
--   if ftype == '11' && !IsFeatureImplemented(FEAT_FP16) then UNDEFINED;
--   constant integer datasize = 8 << UInt(ftype EOR '10');
--   constant bits(4) condition = cond;
--
--   CheckFPEnabled64();
--   bits(datasize) result;
--   result = if ConditionHolds(condition) then V[n, datasize] else V[m, datasize];
--   V[d, 128] = Zeros(128); V[d, datasize] = result;
--
-- Half precision (`ftype = 11`) is not modelled. (VeriISLE has no spec for `MInst.FpuCSel*`.)

import FV.Arm.Insts.Common
import FV.Arm.Insts.DPSFP.FP_data_processing_one_source

namespace Arm

----------------------------------------------------------------------

namespace DPSFP

open _root_.BitVec Arm.BitVec

@[state_simp_rules]
def exec_fp_conditional_select (inst : FP_conditional_select_cls) (s : ArmState) : ArmState :=
  if inst.M = 1#1 ∨ inst.S = 1#1 ∨ inst.ftype = 0b10#2 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else if inst.ftype = 0b11#2 then
    write_err (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!") s
  else
    let datasize := if inst.ftype = 0b01#2 then 64 else 32
    let result := if ConditionHolds inst.cond s then read_sfp datasize inst.Rn s
                  else read_sfp datasize inst.Rm s
    fp_write_result datasize inst.Rd result s

end DPSFP

end Arm
