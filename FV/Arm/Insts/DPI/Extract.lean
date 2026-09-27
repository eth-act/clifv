/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license; see third_party/NOTICE-lnsym.md.
-/
-- (FV addition, not in LNSym) EXTR (32-, 64-bit), including its alias ROR (immediate).
--
-- Transcribed from the Arm ARM (DDI 0487, "EXTR", C6.2.x) ASL:
--
--   integer d = UInt(Rd); integer n = UInt(Rn); integer m = UInt(Rm);
--   constant integer datasize = 32 << UInt(sf);
--   integer lsb;
--   if N != sf then UNDEFINED;
--   if sf == '0' && imms<5> == '1' then UNDEFINED;
--   lsb = UInt(imms);
--
--   bits(datasize) result;
--   bits(datasize) operand1 = X[n, datasize];
--   bits(datasize) operand2 = X[m, datasize];
--   bits(2*datasize) concat = operand1:operand2;
--   result = concat<lsb+datasize-1:lsb>;
--   X[d, datasize] = result;
--
-- Encoding class "Extract" (A64 decode: Data Processing -- Immediate): op21 = 00, o0 = 0.
-- Cross-checked against VeriISLE's ASL-derived `MInst.AluRRRShift`/EXTR use in
-- cranelift/codegen/src/isa/aarch64/spec (the `ror` immediate lowering, `Extr` alu op).

import FV.Arm.Decode
import FV.Arm.Insts.Common

namespace Arm

namespace DPI

open _root_.BitVec Arm.BitVec

@[state_simp_rules]
def exec_extract (inst : Extract_cls) (s : ArmState) : ArmState :=
  if inst.op21 ≠ 0b00#2 ∨ inst.o0 ≠ 0b0#1 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else if inst.N ≠ inst.sf then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else if inst.sf = 0#1 ∧ lsb inst.imms 5 = 1#1 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize := 32 <<< inst.sf.toNat
    let lsb_pos := inst.imms.toNat
    let operand1 := read_gpr_zr datasize inst.Rn s
    let operand2 := read_gpr_zr datasize inst.Rm s
    let concat := operand1 ++ operand2
    let result := extractLsb' lsb_pos datasize concat
    let s := write_gpr_zr datasize inst.Rd result s
    let s := write_pc ((read_pc s) + 4#64) s
    s

end DPI

end Arm
