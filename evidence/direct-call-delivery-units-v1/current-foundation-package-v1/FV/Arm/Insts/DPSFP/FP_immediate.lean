/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license; see third_party/NOTICE-lnsym.md.
-/
-- (FV addition, not in LNSym) Floating-point immediate: FMOV (scalar, immediate), single
-- (`ftype = 00`) and double (`ftype = 01`) precision.
--
-- Transcribed from the Arm ARM (DDI 0487) "FMOV (scalar, immediate)" ASL:
--
--   if ftype == '10' then UNDEFINED;                          // (imm5, M, S nonzero: unallocated)
--   if ftype == '11' && !IsFeatureImplemented(FEAT_FP16) then UNDEFINED;
--   constant integer datasize = 8 << UInt(ftype EOR '10');
--   constant bits(datasize) imm = VFPExpandImm(imm8, datasize);
--
--   CheckFPEnabled64();
--   V[d, 128] = Zeros(128); V[d, datasize] = imm;
--
-- `VFPExpandImm` (shared/functions/float/vfpexpandimm):
--
--   constant integer E = (if N == 16 then 5 elsif N == 32 then 8 else 11);
--   constant integer F = N - E - 1;
--   sign = imm8<7>;
--   exp  = NOT(imm8<6>):Replicate(imm8<6>,E-3):imm8<5:4>;
--   frac = imm8<3:0>:Zeros(F-4);
--   result = sign : exp : frac;
--
-- Half precision (`ftype = 11`) is not modelled. Cross-checked against VeriISLE
-- `MInst.FpuMoveFPImm` (cranelift/codegen/src/isa/aarch64/spec/fpu_move_imm.isle).

import FV.Arm.Insts.Common
import FV.Arm.Insts.DPSFP.FP_data_processing_one_source

namespace Arm

----------------------------------------------------------------------

namespace DPSFP

open _root_.BitVec Arm.BitVec

/-- `VFPExpandImm(imm8, N)` for a format with `E` exponent and `F` fraction bits
(`N = 1 + E + F`, `E ≥ 3`, `F ≥ 4`). -/
def VFPExpandImm (E F : Nat) (imm8 : BitVec 8) : BitVec (1 + E + F) :=
  let v := imm8.toNat
  let b6 := v / 64 % 2
  let exp : Nat := ((1 - b6) <<< (E - 1)) ||| ((b6 * (2 ^ (E - 3) - 1)) <<< 2) ||| (v / 16 % 4)
  let frac : Nat := (v % 16) <<< (F - 4)
  BitVec.ofNat _ (((v / 128) <<< (E + F)) ||| (exp <<< F) ||| frac)

-- `fmov s0, #1.0` (imm8 = 0x70) is 0x3f800000; `fmov d0, #-0.125` (imm8 = 0xc0) is 0xbfc0000000000000.
example : VFPExpandImm 8 23 0x70#8 = 0x3f800000#32 := by decide
example : VFPExpandImm 11 52 0xc0#8 = 0xbfc0000000000000#64 := by decide

@[state_simp_rules]
def exec_fp_immediate (inst : FP_immediate_cls) (s : ArmState) : ArmState :=
  if inst.M = 1#1 ∨ inst.S = 1#1 ∨ inst.ftype = 0b10#2 ∨ inst.imm5 ≠ 0#5 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else if inst.ftype = 0b11#2 then
    write_err (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!") s
  else if inst.ftype = 0b00#2 then
    fp_write_result 32 inst.Rd (VFPExpandImm 8 23 inst.imm8) s
  else
    fp_write_result 64 inst.Rd (VFPExpandImm 11 52 inst.imm8) s

end DPSFP

end Arm
