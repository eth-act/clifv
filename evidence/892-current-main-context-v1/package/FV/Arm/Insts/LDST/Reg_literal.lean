/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license; see third_party/NOTICE-lnsym.md.
-/
-- (FV addition, not in LNSym) Load register (literal): LDR (literal) W/X, LDRSW (literal),
-- LDR (literal, SIMD&FP) S/D/Q. Cranelift loads `f64`/`f128` constants from its constant pool
-- with `ldr d/q, <label>` (`constant_f64` → `fpu_load64 (AMode.Const …)`, `AMode::Label` in
-- `emit.rs`).
--
-- Transcribed from the Arm ARM (DDI 0487) "LDR (literal)", "LDRSW (literal)", "LDR (literal,
-- SIMD&FP)" ASL:
--
--   // GPR (V = 0)                                   // SIMD&FP (V = 1)
--   integer t = UInt(Rt);                            integer t = UInt(Rt);
--   MemOp memop = MemOp_LOAD;                        integer size;
--   boolean signed = FALSE;                          case opc of
--   integer size;                                        when '00' size = 4;
--   case opc of                                          when '01' size = 8;
--       when '00' size = 4;                              when '10' size = 16;
--       when '01' size = 8;                              when '11' UNDEFINED;
--       when '10' size = 4; signed = TRUE;
--       when '11' memop = MemOp_PREFETCH;
--   bits(64) offset = SignExtend(imm19:'00', 64);
--
--   bits(64) address = PC[] + offset;
--   data = Mem[address, size];
--   GPR:      if signed then X[t, 64] = SignExtend(data, 64); else X[t, size*8] = data;
--   SIMD&FP:  V[t, size*8] = data;
--
-- `X[t, n]` writes zero-extend to 64 bits and register 31 is XZR (`write_gpr_zr`); `V[t, n]`
-- zero-extends to 128 bits (`write_sfp`). PRFM (literal) is not modelled.

import FV.Arm.Decode.LDST
import FV.Arm.Insts.Common

namespace Arm

----------------------------------------------------------------------

namespace LDST

open _root_.BitVec Arm.BitVec

/-- The address of a literal load: `PC[] + SignExtend(imm19:'00', 64)`. -/
@[state_simp_rules]
def literal_address (imm19 : BitVec 19) (s : ArmState) : BitVec 64 :=
  read_pc s + signExtend 64 (imm19 ++ 0b00#2)

@[state_simp_rules]
def exec_reg_literal (inst : Reg_literal_cls) (s : ArmState) : ArmState :=
  let address := literal_address inst.imm19 s
  let next (s' : ArmState) : ArmState := write_pc ((read_pc s) + 4#64) s'
  if inst.V = 1#1 then
    match inst.opc with
    | 0b00#2 => next (write_sfp 32 inst.Rt (read_mem_bytes 4 address s) s)
    | 0b01#2 => next (write_sfp 64 inst.Rt (read_mem_bytes 8 address s) s)
    | 0b10#2 => next (write_sfp 128 inst.Rt (read_mem_bytes 16 address s) s)
    | _ => write_err (StateError.Illegal s!"Illegal instruction {inst} encountered!") s
  else
    match inst.opc with
    | 0b00#2 => next (write_gpr_zr 32 inst.Rt (read_mem_bytes 4 address s) s)
    | 0b01#2 => next (write_gpr_zr 64 inst.Rt (read_mem_bytes 8 address s) s)
    | 0b10#2 =>
      next (write_gpr_zr 64 inst.Rt (signExtend 64 (read_mem_bytes 4 address s)) s)
    | _ => write_err (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!") s

end LDST

end Arm
