/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license; see third_party/NOTICE-lnsym.md.
-/
-- (FV addition, not in LNSym) ADD, ADDS, SUB, SUBS (extended register), 32- and 64-bit,
-- including the aliases CMP/CMN (extended register) and `mov`/`add` to and from SP.
--
-- Transcribed from the Arm ARM (DDI 0487) "ADD (extended register)" / "ADDS" / "SUB" / "SUBS"
-- ASL (the four share one decode):
--
--   integer d = UInt(Rd); integer n = UInt(Rn); integer m = UInt(Rm);
--   constant integer datasize = 32 << UInt(sf);
--   ExtendType extend_type = DecodeRegExtend(option);
--   integer shift = UInt(imm3);
--   if shift > 4 then UNDEFINED;
--
--   bits(datasize) result;
--   bits(datasize) operand1 = if n == 31 then SP[datasize] else X[n, datasize];
--   bits(datasize) operand2 = ExtendReg(m, extend_type, shift, datasize);
--   bits(4) nzcv; bit carry_in;
--   if sub_op then operand2 = NOT(operand2); carry_in = '1';
--   else carry_in = '0';
--   (result, nzcv) = AddWithCarry(operand1, operand2, carry_in);
--   if setflags then PSTATE.<N,Z,C,V> = nzcv;
--   if d == 31 && !setflags then SP[] = ZeroExtend(result, 64);
--   else X[d, datasize] = result;
--
-- `opt` (bits 23:22) must be `00`; other values are unallocated.
-- Cross-checked against VeriISLE `MInst.AluRRRExtend` in
-- cranelift/codegen/src/isa/aarch64/spec/alu_rrr_extend.isle.

import FV.Arm.Decode
import FV.Arm.Insts.Common

namespace Arm

namespace DPR

open _root_.BitVec Arm.BitVec

@[state_simp_rules]
def exec_add_sub_ext_reg (inst : Add_sub_ext_reg_cls) (s : ArmState) : ArmState :=
  let shift := inst.imm3.toNat
  if inst.opt ≠ 0b00#2 ∨ shift > 4 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize := 32 <<< inst.sf.toNat
    let sub_op := inst.op = 1#1
    let setflags := inst.S = 1#1
    let extend_type := decode_reg_extend inst.option
    -- Rn = 31 is SP, so `read_gpr` (not `read_gpr_zr`).
    let operand1 := read_gpr datasize inst.Rn s
    -- `ExtendReg` reads `X[m]`, where register 31 is ZR.
    let operand2 := extend_reg (read_gpr_zr datasize inst.Rm s) extend_type shift
    let operand2 := if sub_op then ~~~operand2 else operand2
    let carry := if sub_op then 1#1 else 0#1
    let (result, pstate) := AddWithCarry operand1 operand2 carry
    let s' := write_pc ((read_pc s) + 4#64) s
    let s' := if setflags then write_pstate pstate s' else s'
    let s' := if inst.Rd = 31#5 ∧ ¬ setflags
              then write_gpr datasize inst.Rd result s'
              else write_gpr_zr datasize inst.Rd result s'
    s'

end DPR

end Arm
