/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- REV, REV16, REV32
-- Modified by fv-compiler-rust (2026): ported to Lean v4.34.1, module prefix FV.Arm, wrapped in
-- namespace Arm; RBIT, CLZ and CLS added (`exec_data_processing_rbit`, `..._clz_cls`).

import FV.Arm.Decode
import FV.Arm.Insts.Common

namespace Arm


----------------------------------------------------------------------

namespace DPR

open _root_.BitVec Arm.BitVec

private theorem shiftLeft_ge (x : Nat) (y : Nat) : x ≤ x <<< y := by
  have h₀ : 0 < 2 ^ y := by
    simp only [Nat.zero_lt_two, Nat.pow_pos]
  have h₁ : x ≤ x * 2 ^ y := Nat.le_mul_of_pos_right x h₀
  simp only [Nat.shiftLeft_eq]
  exact h₁

private theorem container_size_le_datasize (opc : Nat) (sf : Nat)
  (h₀ : opc ≥ 0) (h₁ : opc < 4) (h₃ : ¬(opc = 3 ∧ sf = 0)) :
  8 <<< opc ≤ 32 <<< sf := by
  have H1 : 8 = 2 ^ 3 := by decide
  have H2 : 32 = 2 ^ 5 := by decide
  have H3 : 3 + opc ≤ 5 + sf := by omega
  simp only [Nat.shiftLeft_eq, H1, H2, ← Nat.pow_add]
  refine Nat.pow_le_pow_right ?ha H3
  decide

private theorem container_size_dvd_datasize (opc : Nat) (sf : Nat)
  (h₀ : opc ≥ 0) (h₁ : opc < 4) (h₃ : ¬(opc = 3 ∧ sf = 0)):
  (8 <<< opc ∣ 32 <<< sf) := by
  have H1 : 8 = 2 ^ 3 := by decide
  have H2 : 32 = 2 ^ 5 := by decide
  have H3 : 3 + opc ≤ 5 + sf := by omega
  simp only [Nat.shiftLeft_eq, H1, H2, ← Nat.pow_add]
  apply Nat.pow_dvd_pow_iff_le_right'.mpr H3

private theorem opc_and_sf_constraint (x : BitVec 2) (y : BitVec 1)
  (h : ¬(x = 0b11#2 ∧ y = 0b0#1)) :
  ¬(x.toNat = 3 ∧ y.toNat = 0) := by
  revert h
  simp only [BitVec.toNat_eq_nat]
  have h₁ : 3 < 2 ^ 2 := by decide
  simp only [_root_.not_and, Nat.reducePow, h₁, true_and, Nat.pow_one, Nat.zero_lt_succ, imp_self]

@[state_simp_rules]
def exec_data_processing_rev
  (inst : Data_processing_one_source_cls) (s : ArmState) : ArmState :=
  let opc : BitVec 2 := extractLsb' 0 2 inst.opcode
  if H₁ : opc = 0b11#2 ∧ inst.sf = 0b0#1 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize := 32 <<< inst.sf.toNat
    let container_size := 8 <<< opc.toNat
    let operand := read_gpr_zr datasize inst.Rn s
    let esize := 8
    have opc_h₁ : opc.toNat ≥ 0 := by simp only [ge_iff_le, Nat.zero_le]
    have opc_h₂ : opc.toNat < 4 := by
      refine BitVec.isLt (extractLsb' 0 2 inst.opcode)
    have opc_sf_h : ¬(opc.toNat = 3 ∧ inst.sf.toNat = 0) := by
      apply opc_and_sf_constraint (extractLsb' 0 2 inst.opcode) inst.sf H₁
    have h₀ : 0 < esize := by decide
    have h₁ : esize ≤ container_size := by apply shiftLeft_ge
    have h₂ : container_size ≤ datasize := by
      apply container_size_le_datasize opc.toNat inst.sf.toNat opc_h₁ opc_h₂ opc_sf_h
    have h₃ : esize ∣ container_size := by
      simp only [esize, container_size]
      generalize BitVec.toNat (extractLsb' 0 2 inst.opcode) = x
      simp only [Nat.shiftLeft_eq]
      generalize 2 ^ x = n
      simp only [Nat.dvd_mul_right]
    have h₄ : container_size ∣ datasize := by
      apply container_size_dvd_datasize opc.toNat inst.sf.toNat opc_h₁ opc_h₂ opc_sf_h
    let result := rev_vector datasize container_size esize operand h₀ h₁ h₂ h₃ h₄
    -- State Updates
    let s := write_gpr_zr datasize inst.Rd result s
    let s := write_pc ((read_pc s) + 4#64) s
    s

/-- (FV addition) RBIT (32-, 64-bit). Arm ARM (DDI 0487) "RBIT" ASL:
```
bits(datasize) operand = X[n, datasize]; bits(datasize) result;
for i = 0 to datasize-1
    result<datasize-1-i> = operand<i>;
X[d, datasize] = result;
```
This is core `BitVec.reverse` (`getLsbD_reverse`), which `bv_decide` supports natively.
Cross-checked against VeriISLE `MInst.BitRR` (`RBit`) in
cranelift/codegen/src/isa/aarch64/spec/bit_rr.isle. -/
@[state_simp_rules]
def exec_data_processing_rbit
  (inst : Data_processing_one_source_cls) (s : ArmState) : ArmState :=
  let datasize := 32 <<< inst.sf.toNat
  let operand := read_gpr_zr datasize inst.Rn s
  let result := operand.reverse
  let s := write_gpr_zr datasize inst.Rd result s
  let s := write_pc ((read_pc s) + 4#64) s
  s

/-- (FV addition) CLZ / CLS (32-, 64-bit). Arm ARM (DDI 0487) "CLZ"/"CLS" ASL:
```
integer result;
bits(datasize) operand1 = X[n, datasize];
if opcode == CountOp_CLZ then result = CountLeadingZeroBits(operand1);
else                          result = CountLeadingSignBits(operand1);
X[d, datasize] = result<datasize-1:0>;

integer CountLeadingZeroBits(bits(N) x) return N - (HighestSetBit(x) + 1);
integer CountLeadingSignBits(bits(N) x)
    return CountLeadingZeroBits(x<N-1:1> EOR x<N-2:0>);
```
`CountLeadingZeroBits` is core `BitVec.clz` (which yields `N` for `x = 0`, as the ASL does
with `HighestSetBit(0) = -1`). Cross-checked against VeriISLE `MInst.BitRR` (`Clz`, `Cls`) in
cranelift/codegen/src/isa/aarch64/spec/bit_rr.isle. -/
@[state_simp_rules]
def exec_data_processing_clz_cls (cls : Bool)
  (inst : Data_processing_one_source_cls) (s : ArmState) : ArmState :=
  let datasize := 32 <<< inst.sf.toNat
  let operand1 := read_gpr_zr datasize inst.Rn s
  let result : BitVec datasize :=
    if cls then
      zeroExtend datasize
        (BitVec.clz ((extractLsb' 1 (datasize - 1) operand1) ^^^
                     (extractLsb' 0 (datasize - 1) operand1)))
    else
      BitVec.clz operand1
  let s := write_gpr_zr datasize inst.Rd result s
  let s := write_pc ((read_pc s) + 4#64) s
  s

@[state_simp_rules]
def exec_data_processing_one_source
  (inst : Data_processing_one_source_cls) (s : ArmState) : ArmState :=
  match inst.sf, inst.S, inst.opcode2, inst.opcode with
  | _, 0#1, 0b00000#5, 0b000000#6 -- RBIT - 32-, 64-bit
    => exec_data_processing_rbit inst s
  | _, 0#1, 0b00000#5, 0b000100#6 -- CLZ - 32-, 64-bit
    => exec_data_processing_clz_cls false inst s
  | _, 0#1, 0b00000#5, 0b000101#6 -- CLS - 32-, 64-bit
    => exec_data_processing_clz_cls true inst s
  | 0#1, 0#1, 0b00000#5, 0b000001#6 -- REV16 - 32-bit
  | 0#1, 0#1, 0b00000#5, 0b000010#6 -- REV - 32-bit
  | 1#1, 0#1, 0b00000#5, 0b000001#6 -- REV16 - 64-bit
  | 1#1, 0#1, 0b00000#5, 0b000010#6 -- REV32
  | 1#1, 0#1, 0b00000#5, 0b000011#6 -- REV - 64-bit
    => exec_data_processing_rev inst s
  | _, _, _, _ => write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s

----------------------------------------------------------------------

end DPR

end Arm
