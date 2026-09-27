/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Nathan Wetzler
-/
-- MADD, MSUB (32-, 64-bit); SMADDL, SMSUBL, SMULH, UMADDL, UMSUBL, UMULH
-- Modified by fv-compiler-rust (2026): ported to Lean v4.34.1, module prefix FV.Arm, wrapped in
-- namespace Arm; MSUB, SMULH and UMULH implemented (upstream: MADD only), transcribed from the
-- Arm ARM (DDI 0487) ASL (see `exec_data_processing_msub` and `exec_data_processing_mulh`).

import FV.Arm.Decode
import FV.Arm.Insts.Common

namespace Arm


----------------------------------------------------------------------

namespace DPR

open _root_.BitVec Arm.BitVec

@[state_simp_rules]
def exec_data_processing_madd
  (inst : Data_processing_three_source_cls) (s : ArmState) : ArmState :=
  let destsize := 32 <<< inst.sf.toNat
  let operand1 := read_gpr_zr destsize inst.Rn s
  let operand2 := read_gpr_zr destsize inst.Rm s
  let operand3 := read_gpr_zr destsize inst.Ra s
  -- let result := BitVec.add operand3 (BitVec.mul operand1 operand2)
  let result := operand3 + (operand1 * operand2)
  -- State Update
  let s := write_gpr_zr destsize inst.Rd result s
  let s := write_pc ((read_pc s) + 4#64) s
  s

/-- (FV addition) MSUB (32-, 64-bit). Arm ARM (DDI 0487) "MSUB" ASL:
```
bits(datasize) operand1 = X[n, datasize]; bits(datasize) operand2 = X[m, datasize];
bits(datasize) operand3 = X[a, datasize];
integer result = UInt(operand3) - (UInt(operand1) * UInt(operand2));
X[d, datasize] = result<datasize-1:0>;
```
Cross-checked against VeriISLE `MInst.AluRRRR` (`MSub`) in
cranelift/codegen/src/isa/aarch64/spec/alu_rrrr.isle. -/
@[state_simp_rules]
def exec_data_processing_msub
  (inst : Data_processing_three_source_cls) (s : ArmState) : ArmState :=
  let destsize := 32 <<< inst.sf.toNat
  let operand1 := read_gpr_zr destsize inst.Rn s
  let operand2 := read_gpr_zr destsize inst.Rm s
  let operand3 := read_gpr_zr destsize inst.Ra s
  let result := operand3 - (operand1 * operand2)
  -- State Update
  let s := write_gpr_zr destsize inst.Rd result s
  let s := write_pc ((read_pc s) + 4#64) s
  s

/-- (FV addition) SMULH / UMULH (64-bit only). Arm ARM (DDI 0487) "SMULH"/"UMULH" ASL:
```
bits(64) operand1 = X[n, 64]; bits(64) operand2 = X[m, 64];
integer result = Int(operand1, unsigned) * Int(operand2, unsigned);
X[d, 64] = result<127:64>;
```
(`Ra` must be `11111`; other values are unallocated encodings.)
Cross-checked against VeriISLE `MInst.AluRRR` (`SMulH`/`UMulH`) in
cranelift/codegen/src/isa/aarch64/spec/alu_rrr.isle. -/
@[state_simp_rules]
def exec_data_processing_mulh (unsigned : Bool)
  (inst : Data_processing_three_source_cls) (s : ArmState) : ArmState :=
  let operand1 := read_gpr_zr 64 inst.Rn s
  let operand2 := read_gpr_zr 64 inst.Rm s
  let ext : BitVec 64 → BitVec 128 :=
    if unsigned then zeroExtend 128 else signExtend 128
  let result := (ext operand1) * (ext operand2)
  let s := write_gpr_zr 64 inst.Rd (extractLsb' 64 64 result) s
  let s := write_pc ((read_pc s) + 4#64) s
  s

@[state_simp_rules]
def exec_data_processing_three_source
  (inst : Data_processing_three_source_cls) (s : ArmState) : ArmState :=
  let (illegal, unimplemented) :=
    match inst.sf, inst.op54, inst.op31, inst.o0 with
    | _, 0b00#2, 0b010#3, 0b1#1
    | _, 0b00#2, 0b011#3, _
    | _, 0b00#2, 0b100#3, _
    | _, 0b00#2, 0b110#3, 0b1#1
    | _, 0b00#2, 0b111#3, _
    | _, 0b01#2, _, _
    | _, 0b10#2, _, _
    | _, 0b11#2, _, _
      => (true, false) -- Unallocated
    | 0b0#1, 0b00#2, 0b000#3, 0b0#1 => (false, false) -- MADD (32-bit)
    | 0b0#1, 0b00#2, 0b000#3, 0b1#1 => (false, false) -- MSUB (32-bit)
    | 0b0#1, 0b00#2, 0b001#3, 0b0#1
    | 0b0#1, 0b00#2, 0b001#3, 0b1#1
    | 0b0#1, 0b00#2, 0b010#3, 0b0#1
    | 0b0#1, 0b00#2, 0b101#3, 0b0#1
    | 0b0#1, 0b00#2, 0b101#3, 0b1#1
    | 0b0#1, 0b00#2, 0b110#3, 0b0#1
      => (true, false) -- Unallocated
    | 0b1#1, 0b00#2, 0b000#3, 0b0#1 => (false, false) -- MADD (64-bit)
    | 0b1#1, 0b00#2, 0b000#3, 0b1#1 => (false, false) -- MSUB (64-bit)
    | 0b1#1, 0b00#2, 0b001#3, 0b0#1 => (false, true)  -- SMADDL
    | 0b1#1, 0b00#2, 0b001#3, 0b1#1 => (false, true)  -- SMSUBL
    | 0b1#1, 0b00#2, 0b010#3, 0b0#1 => (false, false) -- SMULH
    | 0b1#1, 0b00#2, 0b101#3, 0b0#1 => (false, true)  -- UMADDL
    | 0b1#1, 0b00#2, 0b101#3, 0b1#1 => (false, true)  -- UMSUBL
    | 0b1#1, 0b00#2, 0b110#3, 0b0#1 => (false, false) -- UMULH
    | _, _, _, _ => (true, false)
  if illegal then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else if unimplemented then
    write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s
  else
    match inst.sf, inst.op54, inst.op31, inst.o0 with
    | 0b0#1, 0b00#2, 0b000#3, 0b0#1 => exec_data_processing_madd inst s -- MADD (32-bit)
    | 0b1#1, 0b00#2, 0b000#3, 0b0#1 => exec_data_processing_madd inst s -- MADD (64-bit)
    | 0b0#1, 0b00#2, 0b000#3, 0b1#1 => exec_data_processing_msub inst s -- MSUB (32-bit)
    | 0b1#1, 0b00#2, 0b000#3, 0b1#1 => exec_data_processing_msub inst s -- MSUB (64-bit)
    -- SMULH/UMULH: the `Ra` field is should-be-one (`(1)(1)(1)(1)(1)`); other values are
    -- CONSTRAINED UNPREDICTABLE, and the model (like qemu) ignores it.
    | 0b1#1, 0b00#2, 0b010#3, 0b0#1 => exec_data_processing_mulh false inst s -- SMULH
    | 0b1#1, 0b00#2, 0b110#3, 0b0#1 => exec_data_processing_mulh true inst s  -- UMULH
    | _, _, _, _ => write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s

----------------------------------------------------------------------

end DPR

end Arm
