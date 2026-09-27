/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license; see third_party/NOTICE-lnsym.md.
-/
-- (FV addition, not in LNSym) CCMN, CCMP (immediate and register), 32- and 64-bit.
--
-- Transcribed from the Arm ARM (DDI 0487) "CCMP (immediate)" / "CCMP (register)" /
-- "CCMN (immediate)" / "CCMN (register)" ASL:
--
--   integer n = UInt(Rn);
--   constant integer datasize = 32 << UInt(sf);
--   bits(4) flags = nzcv;
--   bits(datasize) imm = ZeroExtend(imm5, datasize);      // immediate forms
--   // register forms: bits(datasize) operand2 = X[m, datasize];
--
--   bits(datasize) operand1 = X[n, datasize];
--   bits(datasize) operand2 = imm;
--   bit carry_in = '0';
--   if ConditionHolds(cond) then
--       if sub_op then operand2 = NOT(operand2); carry_in = '1';
--       (-, flags) = AddWithCarry(operand1, operand2, carry_in);
--   PSTATE.<N,Z,C,V> = flags;
--
-- `sub_op` is `op == '1'` (CCMP). `S` must be `1`, `o2` and `o3` must be `0`; other values are
-- unallocated. Cross-checked against VeriISLE `MInst.CCmpImm` / `MInst.CCmp` in
-- cranelift/codegen/src/isa/aarch64/spec/conds.isle.

import FV.Arm.Decode
import FV.Arm.Insts.Common

namespace Arm

namespace DPR

open _root_.BitVec Arm.BitVec

/-- Shared body of the immediate and register forms. -/
@[state_simp_rules]
def conditional_compare (sub_op : Bool) (cond : BitVec 4) (nzcv : BitVec 4)
    (operand1 operand2 : BitVec n) (s : ArmState) : ArmState :=
  let flags :=
    if ConditionHolds cond s then
      let operand2 := if sub_op then ~~~operand2 else operand2
      let carry_in := if sub_op then 1#1 else 0#1
      (AddWithCarry operand1 operand2 carry_in).snd
    else
      make_pstate (lsb nzcv 3) (lsb nzcv 2) (lsb nzcv 1) (lsb nzcv 0)
  let s := write_pstate flags s
  let s := write_pc ((read_pc s) + 4#64) s
  s

@[state_simp_rules]
def exec_conditional_compare_imm (inst : Conditional_compare_imm_cls) (s : ArmState) :
    ArmState :=
  if inst.S ≠ 1#1 ∨ inst.o2 ≠ 0#1 ∨ inst.o3 ≠ 0#1 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize := 32 <<< inst.sf.toNat
    let operand1 := read_gpr_zr datasize inst.Rn s
    let imm := zeroExtend datasize inst.imm5
    conditional_compare (inst.op = 1#1) inst.cond inst.nzcv operand1 imm s

@[state_simp_rules]
def exec_conditional_compare_reg (inst : Conditional_compare_reg_cls) (s : ArmState) :
    ArmState :=
  if inst.S ≠ 1#1 ∨ inst.o2 ≠ 0#1 ∨ inst.o3 ≠ 0#1 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize := 32 <<< inst.sf.toNat
    let operand1 := read_gpr_zr datasize inst.Rn s
    let operand2 := read_gpr_zr datasize inst.Rm s
    conditional_compare (inst.op = 1#1) inst.cond inst.nzcv operand1 operand2 s

end DPR

end Arm
