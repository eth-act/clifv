/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license; see third_party/NOTICE-lnsym.md.
-/
-- (FV addition, not in LNSym) Floating-point data-processing (1 source), single (`ftype = 00`)
-- and double (`ftype = 01`) precision: FMOV (register), FABS (scalar), FNEG (scalar).
--
-- Transcribed from the Arm ARM (DDI 0487) "FMOV (register)", "FABS (scalar)", "FNEG (scalar)"
-- (shared decode `aarch64/instrs/float/arithmetic/unary`):
--
--   if ftype == '10' then UNDEFINED;
--   if ftype == '11' && !IsFeatureImplemented(FEAT_FP16) then UNDEFINED;
--   constant integer datasize = 8 << UInt(ftype EOR '10');   // 32, 64 (16: not modelled)
--   FPUnaryOp fpop;
--   case opc of                                              // opcode = '0000':opc
--       when '00' fpop = FPUnaryOp_MOV;
--       when '01' fpop = FPUnaryOp_ABS;
--       when '10' fpop = FPUnaryOp_NEG;
--       when '11' fpop = FPUnaryOp_SQRT;
--
--   CheckFPEnabled64();
--   bits(datasize) result;
--   bits(datasize) operand = V[n, datasize];
--   case fpop of
--       when FPUnaryOp_MOV result = operand;
--       when FPUnaryOp_ABS result = FPAbs(operand, FPCR);
--       when FPUnaryOp_NEG result = FPNeg(operand, FPCR);
--   V[d, 128] = Zeros(128); V[d, datasize] = result;         // `write_sfp` zero-extends
--
-- `FPAbs`/`FPNeg` (shared/functions/float/fpabs, fpneg): with `FPCR.AH = 0` (Linux default; the
-- model fixes FPCR = 0) they only clear / invert the sign bit, also for NaNs.
-- `M = 1` or `S = 1` and the other opcodes of the class are unallocated or not modelled.
-- Cross-checked against VeriISLE `MInst.FpuRR` (`Abs`, `Neg`; spec/fpu_rr.isle).

import FV.Arm.Decode
import FV.Arm.Insts.Common

namespace Arm

----------------------------------------------------------------------

namespace DPSFP

open _root_.BitVec Arm.BitVec

/-- `FPAbs(op, fpcr)` with `FPCR.AH = 0`: `'0' : op<N-2:0>`. -/
def FPAbs (x : BitVec n) : BitVec n := x &&& (allOnes n >>> 1)

/-- `FPNeg(op, fpcr)` with `FPCR.AH = 0`: `NOT(op<N-1>) : op<N-2:0>`. -/
def FPNeg (x : BitVec n) : BitVec n := x ^^^ ~~~(allOnes n >>> 1)

/-- `V[d, datasize] = result`, then the next instruction. -/
@[state_simp_rules]
def fp_write_result (datasize : Nat) (Rd : BitVec 5) (result : BitVec datasize) (s : ArmState)
    : ArmState :=
  write_pc ((read_pc s) + 4#64) (write_sfp datasize Rd result s)

@[state_simp_rules]
def exec_fp_data_processing_one_source
  (inst : FP_data_processing_one_source_cls) (s : ArmState) : ArmState :=
  if inst.M = 1#1 ∨ inst.S = 1#1 ∨ inst.ftype = 0b10#2 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else if inst.ftype = 0b11#2 then
    write_err (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!") s
  else
    let datasize := if inst.ftype = 0b01#2 then 64 else 32
    let operand := read_sfp datasize inst.Rn s
    match inst.opcode with
    | 0b000000#6 => fp_write_result datasize inst.Rd operand s
    | 0b000001#6 => fp_write_result datasize inst.Rd (FPAbs operand) s
    | 0b000010#6 => fp_write_result datasize inst.Rd (FPNeg operand) s
    | _ => write_err (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!") s

end DPSFP

end Arm
