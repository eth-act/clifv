/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license; see third_party/NOTICE-lnsym.md.
-/
-- (FV addition, not in LNSym) Floating-point data-processing (3 source), single (`ftype = 00`)
-- and double (`ftype = 01`) precision: FMADD, FMSUB, FNMADD, FNMSUB.
--
-- Transcribed from the Arm ARM (DDI 0487) "FMADD", "FMSUB", "FNMADD", "FNMSUB" ASL
-- (`aarch64/instrs/float/arithmetic/mul-add`):
--
--   if ftype == '10' then UNDEFINED;                 // (M, S nonzero: unallocated)
--   constant integer datasize = 8 << UInt(ftype EOR '10');
--   constant boolean opa_neg = (o1 == '1');
--   constant boolean op1_neg = (o1 != o0);
--
--   bits(datasize) operanda = V[a, datasize];
--   bits(datasize) operand1 = V[n, datasize];
--   bits(datasize) operand2 = V[m, datasize];
--   if opa_neg then operanda = FPNeg(operanda, FPCR);
--   if op1_neg then operand1 = FPNeg(operand1, FPCR);
--   result = FPMulAdd(operanda, operand1, operand2, FPCR);
--   V[d, 128] = Zeros(128); V[d, datasize] = result;
--
-- `FPMulAdd(addend, op1, op2)` is `IEEE.mulAdd f rm addend op1 op2` (one rounding, `.rne` with
-- FPCR = 0). Half precision is not modelled.

import FV.Arm.Insts.Common
import FV.Arm.Insts.DPSFP.FP_data_processing_one_source

namespace Arm

----------------------------------------------------------------------

namespace DPSFP

open _root_.BitVec Arm.BitVec

@[state_simp_rules]
def exec_fp_data_processing_three_source (inst : FP_data_processing_three_source_cls)
    (s : ArmState) : ArmState :=
  if inst.M = 1#1 ∨ inst.S = 1#1 ∨ inst.ftype = 0b10#2 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else if inst.ftype = 0b11#2 then
    write_err (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!") s
  else
    let f := fpFmt inst.ftype
    let opa := read_sfp f.N inst.Ra s
    let op1 := read_sfp f.N inst.Rn s
    let op2 := read_sfp f.N inst.Rm s
    let opa := if inst.o1 = 1#1 then IEEE.neg f opa else opa
    let op1 := if inst.o1 ≠ inst.o0 then IEEE.neg f op1 else op1
    fp_write_result f.N inst.Rd (IEEE.mulAdd f .rne opa op1 op2) s

end DPSFP

end Arm
