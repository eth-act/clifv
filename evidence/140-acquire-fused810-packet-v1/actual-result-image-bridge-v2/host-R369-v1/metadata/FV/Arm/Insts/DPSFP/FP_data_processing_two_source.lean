/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license; see third_party/NOTICE-lnsym.md.
-/
-- (FV addition, not in LNSym) Floating-point data-processing (2 source), single (`ftype = 00`)
-- and double (`ftype = 01`) precision: FMUL, FDIV, FADD, FSUB, FMAX, FMIN, FNMUL (scalar).
--
-- Transcribed from the Arm ARM (DDI 0487) "FADD (scalar)", "FSUB (scalar)", "FMUL (scalar)",
-- "FDIV (scalar)", "FMAX (scalar)", "FMIN (scalar)", "FNMUL (scalar)" ASL
-- (`aarch64/instrs/float/arithmetic/{add-sub,mul-div,max-min}`):
--
--   if ftype == '10' then UNDEFINED;                 // (M, S nonzero: unallocated)
--   constant integer datasize = 8 << UInt(ftype EOR '10');
--   bits(datasize) operand1 = V[n, datasize];
--   bits(datasize) operand2 = V[m, datasize];
--   FADD: result = FPAdd(operand1, operand2, FPCR);   FSUB: result = FPSub(…);
--   FMUL: result = FPMul(operand1, operand2, FPCR);   FDIV: result = FPDiv(…);
--   FMAX: result = FPMax(operand1, operand2, FPCR);   FMIN: result = FPMin(…);
--   FNMUL: result = FPNeg(FPMul(operand1, operand2, FPCR), FPCR);
--   V[d, 128] = Zeros(128); V[d, datasize] = result;
--
-- With FPCR = 0 (`docs/decisions/arm-model.md`) the rounding is to nearest even (`.rne`); the
-- functions are the shared IEEE core's (`IEEE.add` …, `docs/contracts/float.md`). FMAXNM and
-- FMINNM (opcode 0110/0111) and half precision are not modelled.

import FV.Arm.Insts.Common
import FV.Arm.Insts.DPSFP.FP_data_processing_one_source

namespace Arm

----------------------------------------------------------------------

namespace DPSFP

open _root_.BitVec Arm.BitVec

@[state_simp_rules]
def exec_fp_data_processing_two_source (inst : FP_data_processing_two_source_cls) (s : ArmState) :
    ArmState :=
  if inst.M = 1#1 ∨ inst.S = 1#1 ∨ inst.ftype = 0b10#2 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else if inst.ftype = 0b11#2 then
    write_err (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!") s
  else
    let f := fpFmt inst.ftype
    let op1 := read_sfp f.N inst.Rn s
    let op2 := read_sfp f.N inst.Rm s
    match inst.opcode with
    | 0b0000#4 => fp_write_result f.N inst.Rd (IEEE.mul f .rne op1 op2) s
    | 0b0001#4 => fp_write_result f.N inst.Rd (IEEE.div f .rne op1 op2) s
    | 0b0010#4 => fp_write_result f.N inst.Rd (IEEE.add f .rne op1 op2) s
    | 0b0011#4 => fp_write_result f.N inst.Rd (IEEE.sub f .rne op1 op2) s
    | 0b0100#4 => fp_write_result f.N inst.Rd (IEEE.max f .rne op1 op2) s
    | 0b0101#4 => fp_write_result f.N inst.Rd (IEEE.min f .rne op1 op2) s
    | 0b1000#4 => fp_write_result f.N inst.Rd (IEEE.neg f (IEEE.mul f .rne op1 op2)) s
    | _ => write_err (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!") s

end DPSFP

end Arm
