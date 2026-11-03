/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license; see third_party/NOTICE-lnsym.md.
-/
-- (FV addition, not in LNSym) Floating-point compare: FCMP, FCMPE (register and `#0.0`), single
-- (`ftype = 00`) and double (`ftype = 01`) precision.
--
-- Transcribed from the Arm ARM (DDI 0487) "FCMP", "FCMPE" ASL
-- (`aarch64/instrs/float/compare/uncond`):
--
--   if ftype == '10' then UNDEFINED;                 // (M, S, op, opcode2<2:0> nonzero: unallocated)
--   constant integer datasize = 8 << UInt(ftype EOR '10');
--   constant boolean signal_all_nans = (opc<1> == '1');   // opcode2<4>: FCMPE
--   constant boolean cmp_with_zero = (opc<0> == '1');     // opcode2<3>: #0.0
--
--   bits(datasize) operand1 = V[n, datasize];
--   bits(datasize) operand2 = if cmp_with_zero then FPZero('0', datasize) else V[m, datasize];
--   PSTATE.<N,Z,C,V> = FPCompare(operand1, operand2, signal_all_nans, FPCR);
--
-- `FPCompare` (shared/functions/float/fpcompare): unordered `0011`, equal `0110`, less than
-- `1000`, greater than `0010` (`IEEE.compare`); `signal_all_nans` only changes the exception
-- flags, which are not modelled, so FCMPE = FCMP. Half precision is not modelled.

import FV.Arm.Insts.Common
import FV.Arm.Insts.DPSFP.FP_data_processing_one_source

namespace Arm

----------------------------------------------------------------------

namespace DPSFP

open _root_.BitVec Arm.BitVec

/-- The NZCV value of an `FPCompare` result. -/
def fpCompareNZCV : IEEE.Cmp → BitVec 4
  | .un => 0b0011#4 | .eq => 0b0110#4 | .lt => 0b1000#4 | .gt => 0b0010#4

@[state_simp_rules]
def exec_fp_compare (inst : FP_compare_cls) (s : ArmState) : ArmState :=
  if inst.M = 1#1 ∨ inst.S = 1#1 ∨ inst.ftype = 0b10#2 ∨ inst.op ≠ 0b00#2 ∨
      extractLsb' 0 3 inst.opcode2 ≠ 0b000#3 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else if inst.ftype = 0b11#2 then
    write_err (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!") s
  else
    let f := fpFmt inst.ftype
    let op1 := read_sfp f.N inst.Rn s
    let op2 := if lsb inst.opcode2 3 = 1#1 then IEEE.zero f false else read_sfp f.N inst.Rm s
    let nzcv := fpCompareNZCV (IEEE.compare f op1 op2)
    let s := write_pstate (make_pstate (lsb nzcv 3) (lsb nzcv 2) (lsb nzcv 1) (lsb nzcv 0)) s
    write_pc ((read_pc s) + 4#64) s

end DPSFP

end Arm
