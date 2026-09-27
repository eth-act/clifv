/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- LSLV, LSRV, ASRV, RORV (32-, 64-bit)
-- Modified by fv-compiler-rust (2026): ported to Lean v4.34.1, module prefix FV.Arm, wrapped in
-- namespace Arm; UDIV and SDIV added (`exec_data_processing_div`).

import FV.Arm.Decode
import FV.Arm.Insts.Common

namespace Arm


----------------------------------------------------------------------

namespace DPR

open _root_.BitVec Arm.BitVec

@[state_simp_rules]
def exec_data_processing_shift
  (inst : Data_processing_two_source_cls) (s : ArmState) : ArmState :=
  let datasize := 32 <<< inst.sf.toNat
  let shift_type := decode_shift $ extractLsb' 0 2 inst.opcode
  let operand2 := read_gpr_zr datasize inst.Rm s
  let amount := BitVec.ofInt 6 (operand2.toInt % datasize)
  let operand := read_gpr_zr datasize inst.Rn s
  let result := shift_reg operand shift_type amount
  -- State Update
  let s := write_gpr_zr datasize inst.Rd result s
  let s := write_pc ((read_pc s) + 4#64) s
  s

/-- (FV addition) UDIV / SDIV (32-, 64-bit). Arm ARM (DDI 0487) "UDIV"/"SDIV" ASL:
```
bits(datasize) operand1 = X[n, datasize]; bits(datasize) operand2 = X[m, datasize];
integer result;
if IsZero(operand2) then result = 0;
else result = RoundTowardsZero(Real(Int(operand1, unsigned)) / Real(Int(operand2, unsigned)));
X[d, datasize] = result<datasize-1:0>;
```
Division by zero yields 0 (no trap). For SDIV, `INT_MIN / -1` yields `INT_MIN`
(the low `datasize` bits of `2^(datasize-1)`). Core `BitVec.udiv` already returns 0 for a zero
divisor; `BitVec.sdiv` rounds towards zero but returns `-1`/`1` for a zero divisor per SMT-LIB,
so the zero case is handled explicitly. Cross-checked against VeriISLE `MInst.AluRRR`
(`UDiv`/`SDiv`) in cranelift/codegen/src/isa/aarch64/spec/alu_rrr.isle. -/
@[state_simp_rules]
def exec_data_processing_div (unsigned : Bool)
  (inst : Data_processing_two_source_cls) (s : ArmState) : ArmState :=
  let datasize := 32 <<< inst.sf.toNat
  let operand1 := read_gpr_zr datasize inst.Rn s
  let operand2 := read_gpr_zr datasize inst.Rm s
  let result :=
    if operand2 = 0#datasize then 0#datasize
    else if unsigned then operand1.udiv operand2
    else operand1.sdiv operand2
  let s := write_gpr_zr datasize inst.Rd result s
  let s := write_pc ((read_pc s) + 4#64) s
  s

@[state_simp_rules]
def exec_data_processing_two_source
  (inst : Data_processing_two_source_cls) (s : ArmState) : ArmState :=
  match inst.S, inst.opcode with
  | 0b0#1, 0b000010#6 -- UDIV 32-, 64-bit
    => exec_data_processing_div true inst s
  | 0b0#1, 0b000011#6 -- SDIV 32-, 64-bit
    => exec_data_processing_div false inst s
  | 0b0#1, 0b001000#6 -- LSLV 32-, 64-bit
  | 0b0#1, 0b001001#6 -- LSRV 32-, 64-bit
  | 0b0#1, 0b001010#6 -- ASRV 32-, 64-bit
  | 0b0#1, 0b001011#6 -- RORV 32-, 64-bit
    => exec_data_processing_shift inst s
  | _, _ => write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s

----------------------------------------------------------------------

end DPR

end Arm
