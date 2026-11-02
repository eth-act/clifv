/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license; see third_party/NOTICE-lnsym.md.
-/
-- (FV addition, not in LNSym) Floating-point data-processing (1 source), single (`ftype = 00`)
-- and double (`ftype = 01`) precision: FMOV (register), FABS (scalar), FNEG (scalar),
-- FSQRT (scalar), FCVT (single ↔ double), FRINTN/P/M/Z/A/X/I (scalar).
--
-- Transcribed from the Arm ARM (DDI 0487) "FMOV (register)", "FABS (scalar)", "FNEG (scalar)",
-- "FSQRT (scalar)" (shared decode `aarch64/instrs/float/arithmetic/unary`):
--
--   if ftype == '10' then UNDEFINED;
--   if ftype == '11' && !IsFeatureImplemented(FEAT_FP16) then UNDEFINED;
--   constant integer datasize = 8 << UInt(ftype EOR '10');   // 32, 64 (16: not modelled)
--   case opc of                                              // opcode = '0000':opc
--       when '00' fpop = FPUnaryOp_MOV;   when '01' fpop = FPUnaryOp_ABS;
--       when '10' fpop = FPUnaryOp_NEG;   when '11' fpop = FPUnaryOp_SQRT;
--
--   bits(datasize) operand = V[n, datasize];
--   case fpop of
--       when FPUnaryOp_MOV  result = operand;
--       when FPUnaryOp_ABS  result = FPAbs(operand, FPCR);
--       when FPUnaryOp_NEG  result = FPNeg(operand, FPCR);
--       when FPUnaryOp_SQRT result = FPSqrt(operand, FPCR);
--   V[d, 128] = Zeros(128); V[d, datasize] = result;         // `write_sfp` zero-extends
--
-- "FCVT" (`aarch64/instrs/float/convert/fp`, opcode = '0001':opc):
--
--   if ftype == opc then UNDEFINED;
--   srcsize per ftype, dstsize per opc ('00' 32, '01' 64, '10' UNDEFINED, '11' 16);
--   bits(srcsize) operand = V[n, srcsize];
--   V[d, 128] = Zeros(128); V[d, dstsize] = FPConvert(operand, FPCR);
--
-- "FRINTN/P/M/Z/A/X/I (scalar)" (`aarch64/instrs/float/arithmetic/round/frint`,
-- opcode = '001':rmode):
--
--   case rmode of
--       when '0xx' rounding = FPDecodeRounding(rmode<1:0>); exact = FALSE;  // N, P, M, Z
--       when '100' rounding = FPRounding_TIEAWAY;            exact = FALSE;  // A
--       when '101' UNDEFINED;
--       when '110' rounding = FPRoundingMode(FPCR);          exact = TRUE;   // X
--       when '111' rounding = FPRoundingMode(FPCR);          exact = FALSE;  // I
--   result = FPRoundInt(operand, FPCR, rounding, exact);
--   V[d, 128] = Zeros(128); V[d, datasize] = result;
--
-- The operations are the shared IEEE core's (`IEEE.abs`, `IEEE.neg`, `IEEE.sqrt`,
-- `IEEE.convert`, `IEEE.roundInt`; `docs/contracts/float.md`) with FPCR = 0
-- (`docs/decisions/arm-model.md`): `FPCR.RMode` is round to nearest even (`.rne`), `AH = 0`
-- (FABS/FNEG only clear / invert the sign bit, also for NaNs), `DN = FZ = 0`; `exact` only
-- raises the Inexact flag, which is not modelled, so FRINTX = FRINTI. `M = 1`, `S = 1`, half
-- precision and the other opcodes of the class (BFCVT, FRINT32/64*) are unallocated or not
-- modelled. Cross-checked against VeriISLE `MInst.FpuRR`, `MInst.FpuRound`
-- (cranelift/codegen/src/isa/aarch64/spec/{fpu_rr,fpu_round}.isle).

import FV.Arm.Decode.DPSFP
import FV.Arm.Insts.Common
import FV.Float

namespace Arm

----------------------------------------------------------------------

namespace DPSFP

open _root_.BitVec Arm.BitVec

/-- The IEEE format of `ftype` `00` (binary32) / `01` (binary64). -/
def fpFmt (ftype : BitVec 2) : IEEE.Fmt := if ftype = 0b01#2 then .b64 else .b32

/-- `FPDecodeRounding(rmode)`: `00` RN, `01` RP, `10` RM, `11` RZ. -/
def FPDecodeRounding (rmode : BitVec 2) : IEEE.RMode :=
  match rmode with
  | 0b00#2 => .rne | 0b01#2 => .rpi | 0b10#2 => .rmi | _ => .rz

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
    let f := fpFmt inst.ftype
    let operand := read_sfp f.N inst.Rn s
    let frint (rm : IEEE.RMode) : ArmState :=
      fp_write_result f.N inst.Rd (IEEE.roundInt f rm operand) s
    match inst.opcode with
    | 0b000000#6 => fp_write_result f.N inst.Rd operand s
    | 0b000001#6 => fp_write_result f.N inst.Rd (IEEE.abs f operand) s
    | 0b000010#6 => fp_write_result f.N inst.Rd (IEEE.neg f operand) s
    | 0b000011#6 => fp_write_result f.N inst.Rd (IEEE.sqrt f .rne operand) s
    -- FCVT Dd, Sn / FCVT Sd, Dn (`ftype = opc` is UNDEFINED; to/from half: not modelled)
    | 0b000100#6 =>
      if inst.ftype = 0b00#2 then
        write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
      else
        fp_write_result 32 inst.Rd (IEEE.convert .b64 .b32 .rne (read_sfp 64 inst.Rn s)) s
    | 0b000101#6 =>
      if inst.ftype = 0b01#2 then
        write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
      else
        fp_write_result 64 inst.Rd (IEEE.convert .b32 .b64 .rne (read_sfp 32 inst.Rn s)) s
    | 0b001000#6 => frint .rne
    | 0b001001#6 => frint .rpi
    | 0b001010#6 => frint .rmi
    | 0b001011#6 => frint .rz
    | 0b001100#6 => frint .rna
    | 0b001110#6 => frint .rne
    | 0b001111#6 => frint .rne
    | _ => write_err (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!") s

end DPSFP

end Arm
