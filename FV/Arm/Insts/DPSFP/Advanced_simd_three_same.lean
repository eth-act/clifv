/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Yan Peng
-/
-- ADD, ORR, AND, BIC, ORR, ORN, EOR, BSL, BIT, BIF (vector)
-- Modified by fv-compiler-rust (2026): ported to Lean v4.34.1, module prefix FV.Arm, wrapped in
-- namespace Arm; ADDP (vector) added (`exec_addp_vector`).

import FV.Arm.Decode
import FV.Arm.State
import FV.Arm.Insts.Common
import FV.Arm.BitVec

namespace Arm


----------------------------------------------------------------------

namespace DPSFP

open _root_.BitVec Arm.BitVec

def binary_vector_op_aux (e : Nat) (elems : Nat) (esize : Nat)
  (op : BitVec esize → BitVec esize → BitVec esize)
  (x : BitVec n) (y : BitVec n) (result : BitVec n) : BitVec n :=
  if elems ≤ e then
    result
  else
    let element1 := elem_get x e esize
    let element2 := elem_get y e esize
    let elem_result := op element1 element2
    let result := elem_set result e esize elem_result
    binary_vector_op_aux (e + 1) elems esize op x y result
  termination_by (elems - e)

theorem binary_vector_op_aux_of_lt {n} {e elems} (h : e < elems) (esize op)
    (x y result : BitVec n) :
    binary_vector_op_aux e elems esize op x y result
    = let element1 := elem_get x e esize
      let element2 := elem_get y e esize
      let elem_result := op element1 element2
      let result := elem_set result e esize elem_result
      binary_vector_op_aux (e + 1) elems esize op x y result := by
  conv => { lhs; unfold binary_vector_op_aux }
  have : ¬(elems ≤ e) := by omega
  simp only [this, ↓reduceIte]

theorem binary_vector_op_aux_of_not_lt {n} {e elems} (h : ¬(e < elems))
    (esize op) (x y result : BitVec n) :
    binary_vector_op_aux e elems esize op x y result = result := by
  unfold binary_vector_op_aux
  simp only [ite_eq_left_iff, Nat.not_le, h, false_implies]

/--
  Perform pairwise op on esize-bit slices of x and y
-/
@[state_simp_rules]
def binary_vector_op (esize : Nat) (op : BitVec esize → BitVec esize → BitVec esize)
  (x : BitVec n) (y : BitVec n) : BitVec n :=
  binary_vector_op_aux 0 (n / esize) esize op x y (BitVec.zero n)

@[state_simp_rules]
def exec_binary_vector (inst : Advanced_simd_three_same_cls) (s : ArmState) : ArmState :=
  if inst.size = 0b11#2 ∧ inst.Q = 0b0#1 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize := if inst.Q = 1#1 then 128 else 64
    let esize := 8 <<< (BitVec.toNat inst.size)
    let sub_op := inst.U = 1
    let operand1 := read_sfp datasize inst.Rn s
    let operand2 := read_sfp datasize inst.Rm s
    let op := if sub_op then BitVec.sub else BitVec.add
    let result := binary_vector_op esize op operand1 operand2
    let s := write_sfp datasize inst.Rd result s
    s

@[state_simp_rules]
def decode_logical_op (U : BitVec 1) (size : BitVec 2) : SIMDThreeSameLogicalType :=
  match U, size with
  | 0#1, 0b00#2 => SIMDThreeSameLogicalType.AND
  | 0#1, 0b01#2 => SIMDThreeSameLogicalType.BIC
  | 0#1, 0b10#2 => SIMDThreeSameLogicalType.ORR
  | 0#1, 0b11#2 => SIMDThreeSameLogicalType.ORN
  | 1#1, 0b00#2 => SIMDThreeSameLogicalType.EOR
  | 1#1, 0b01#2 => SIMDThreeSameLogicalType.BSL
  | 1#1, 0b10#2 => SIMDThreeSameLogicalType.BIT
  | 1#1, 0b11#2 => SIMDThreeSameLogicalType.BIF

@[state_simp_rules]
def logic_vector_op (op : SIMDThreeSameLogicalType) (opdn : BitVec n) (opdm : BitVec n) (opdd : BitVec n)
  : (BitVec n) :=
  match op with
  | SIMDThreeSameLogicalType.AND => opdn &&& opdm
  | SIMDThreeSameLogicalType.BIC => opdn &&& ~~~opdm
  | SIMDThreeSameLogicalType.ORR => opdn ||| opdm
  | SIMDThreeSameLogicalType.ORN => opdn ||| ~~~opdm
  | SIMDThreeSameLogicalType.EOR => opdn ^^^ opdm
  | SIMDThreeSameLogicalType.BSL => opdm ^^^ ((opdm ^^^ opdn) &&& opdd)
  | SIMDThreeSameLogicalType.BIT => opdd ^^^ ((opdd ^^^ opdn) &&& opdm)
  | SIMDThreeSameLogicalType.BIF => opdd ^^^ ((opdd ^^^ opdn) &&& ~~~opdm)

@[state_simp_rules]
def exec_logic_vector (inst : Advanced_simd_three_same_cls) (s : ArmState) : ArmState :=
  let datasize := if inst.Q = 1#1 then 128 else 64
  let operand1 := read_sfp datasize inst.Rn s
  let operand2 := read_sfp datasize inst.Rm s
  let operand3 := read_sfp datasize inst.Rd s
  let op := decode_logical_op inst.U inst.size
  let result := logic_vector_op op operand1 operand2 operand3
  let s := write_sfp datasize inst.Rd result s
  s

/-- (FV addition) Pairwise add of adjacent elements of `concat`. -/
def addp_aux (e : Nat) (elements : Nat) (esize : Nat) (concat : BitVec m)
  (result : BitVec n) : BitVec n :=
  if elements ≤ e then
    result
  else
    let element1 := elem_get concat (2 * e) esize
    let element2 := elem_get concat (2 * e + 1) esize
    let result := elem_set result e esize (element1 + element2)
    addp_aux (e + 1) elements esize concat result
  termination_by (elements - e)

/-- (FV addition) ADDP (vector). Arm ARM (DDI 0487) "ADDP (vector)" ASL (Advanced SIMD three
same, `U = 0`, `opcode = 10111`):
```
if size:Q == '110' then UNDEFINED;
constant integer esize = 8 << UInt(size); constant integer datasize = 64 << UInt(Q);
constant integer elements = datasize DIV esize;
bits(datasize) operand1 = V[n, datasize]; bits(datasize) operand2 = V[m, datasize];
bits(datasize) result;
bits(2*datasize) concat = operand2:operand1;
bits(esize) element1; bits(esize) element2;
for e = 0 to elements-1
    element1 = Elem[concat, 2*e, esize];
    element2 = Elem[concat, (2*e)+1, esize];
    Elem[result, e, esize] = element1 + element2;
V[d, datasize] = result;
```
Cross-checked against VeriISLE `MInst.VecRRR` (`Addp`) in
cranelift/codegen/src/isa/aarch64/spec/vec_rrr.isle. -/
@[state_simp_rules]
def exec_addp_vector (inst : Advanced_simd_three_same_cls) (s : ArmState) : ArmState :=
  if inst.size = 0b11#2 ∧ inst.Q = 0b0#1 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize := if inst.Q = 1#1 then 128 else 64
    let esize := 8 <<< (BitVec.toNat inst.size)
    let operand1 := read_sfp datasize inst.Rn s
    let operand2 := read_sfp datasize inst.Rm s
    let concat := operand2 ++ operand1
    let result := addp_aux 0 (datasize / esize) esize concat (BitVec.zero datasize)
    let s := write_sfp datasize inst.Rd result s
    s

@[state_simp_rules]
def exec_advanced_simd_three_same
  (inst : Advanced_simd_three_same_cls) (s : ArmState) : ArmState :=
  open _root_.BitVec Arm.BitVec in
  let s :=
    match inst.U, inst.opcode with
    | _, 0b10000#5 => exec_binary_vector inst s
    | _, 0b00011#5 => exec_logic_vector inst s
    | 0#1, 0b10111#5 => exec_addp_vector inst s
    | _, _ =>
      write_err (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!") s
  write_pc ((read_pc s) + 4#64) s

theorem pc_of_exec_advanced_simd_three_same
  (h_step : s' = exec_advanced_simd_three_same inst s)
  (h_no_err: read_err s' = None) :
  r StateField.PC s' =
  -- (r StateField.PC s) + 4#64 -- TODO: How do I use + here?
  (BitVec.add (r StateField.PC s) 4#64) := by
  simp_all!
  simp only [exec_advanced_simd_three_same, exec_binary_vector,
             Bool.and_eq_true, beq_iff_eq, binary_vector_op,
             ofNat_eq_ofNat, zero_eq, exec_logic_vector,
             logic_vector_op, exec_addp_vector]
  split
  · split <;> simp only [state_simp_rules, minimal_theory]
  · simp only [state_simp_rules, minimal_theory]
  · split <;> simp only [state_simp_rules, minimal_theory]
  · simp only [state_simp_rules, minimal_theory]

----------------------------------------------------------------------

end DPSFP

end Arm
