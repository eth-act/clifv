/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license; see third_party/NOTICE-lnsym.md.
-/
-- (FV addition; the classes are ported from LNSym's `Advanced_simd_shift_by_immediate_cls` and
-- `Advanced_simd_scalar_shift_by_immediate_cls`) Advanced SIMD shift by immediate (vector) and
-- Advanced SIMD scalar shift by immediate: USHR and SLI. Cranelift's scalar `fcopysign`
-- (`fcopy_sign`, isa/aarch64/inst.isle) emits `ushr vT.2s, vY.2s, #31; sli vX.2s, vT.2s, #31`
-- (f32) and `ushr dT, dY, #63; sli dX, dT, #63` (f64) (`MInst.FpuRRI`/`FpuRRIMod`).
--
-- Transcribed from the Arm ARM (DDI 0487) "USHR", "SLI" ASL
-- (`aarch64/instrs/vector/shift/right/simd`, `.../right/sisd`, `.../leftinsert/simd`,
-- `.../leftinsert/sisd`). Decode, vector:
--
--   if immh == '0000' then SEE(asimdimm);          // decoded as modified immediate
--   if immh<3>:Q == '10' then UNDEFINED;
--   constant integer esize = 8 << HighestSetBit(immh);
--   constant integer datasize = 64 << UInt(Q);
--   constant integer elements = datasize DIV esize;
--   USHR: constant integer shift = (esize * 2) - UInt(immh:immb);
--   SLI:  constant integer shift = UInt(immh:immb) - esize;
--
-- Decode, scalar:
--
--   if immh<3> != '1' then UNDEFINED;
--   constant integer esize = 8 << 3;
--   constant integer datasize = esize;
--   constant integer elements = 1;
--   USHR: constant integer shift = (esize * 2) - UInt(immh:immb);
--   SLI:  constant integer shift = UInt(immh:immb) - esize;
--
-- Operation, USHR (U = 1, o1 = 0: no rounding, o0 = 0: no accumulation):
--
--   bits(datasize) operand  = V[n, datasize];
--   bits(datasize) operand2 = Zeros(datasize);     // accumulate == FALSE
--   bits(datasize) result;
--   constant integer round_const = 0;              // round == FALSE
--   for e = 0 to elements-1
--       element = (UInt(Elem[operand, e, esize]) + round_const) >> shift;
--       Elem[result, e, esize] = Elem[operand2, e, esize] + element<esize-1:0>;
--   V[d, datasize] = result;
--
-- that is `Elem[result, e, esize] = Elem[operand, e, esize] >>> shift` (a logical shift; `shift`
-- is in `1 ..= esize` and `>>> esize` is zero, as `UInt(x) >> esize` is). Operation, SLI:
--
--   bits(datasize) operand  = V[n, datasize];
--   bits(datasize) operand2 = V[d, datasize];
--   bits(datasize) result;
--   bits(esize) mask = LSL(Ones(esize), shift);
--   bits(esize) shifted;
--   for e = 0 to elements-1
--       shifted = LSL(Elem[operand, e, esize], shift);
--       Elem[result, e, esize] = (Elem[operand2, e, esize] AND NOT(mask)) OR shifted;
--   V[d, datasize] = result;
--
-- `V[d, datasize] = result` with `datasize < 128` zeroes the upper bits (`write_sfp`). The
-- element loops are `binary_vector_op` (Advanced_simd_three_same.lean). Modelled: USHR and SLI
-- at every element size and `Q` the ASL allows; the other instructions of the two classes (SHL,
-- SSHR, SSRA, USRA, SRSHR, URSHR, SRSRA, URSRA, SRI, SQSHL, UQSHL, SQSHLU, the narrowing and
-- long shifts, SCVTF/UCVTF/FCVTZS/FCVTZU (fixed-point)) are `StateError.Unimplemented`.

import FV.Arm.Decode.DPSFP
import FV.Arm.Insts.Common
import FV.Arm.Insts.DPSFP.Advanced_simd_three_same

namespace Arm

----------------------------------------------------------------------

namespace DPSFP

open _root_.BitVec Arm.BitVec

/-- USHR on every `esize`-bit element of `operand`: `Elem[operand, e, esize] >>> shift`. -/
def ushr_vector (esize shift : Nat) (operand : BitVec n) : BitVec n :=
  binary_vector_op esize (fun element _ => element >>> shift) operand operand

/-- SLI on every `esize`-bit element: `(Elem[operand2, e, esize] AND NOT(mask)) OR
LSL(Elem[operand, e, esize], shift)` with `mask = LSL(Ones(esize), shift)`; `operand2` is the old
destination. -/
def sli_vector (esize shift : Nat) (operand operand2 : BitVec n) : BitVec n :=
  let mask : BitVec esize := allOnes esize <<< shift
  binary_vector_op esize (fun element1 element2 => (element2 &&& ~~~mask) ||| (element1 <<< shift))
    operand operand2

@[state_simp_rules]
def exec_ushr_vector (inst : Advanced_simd_shift_by_immediate_cls) (s : ArmState) : ArmState :=
  if lsb inst.immh 3 ++ inst.Q = 0b10#2 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let esize := 8 <<< highest_set_bit inst.immh
    let datasize := 64 <<< inst.Q.toNat
    let shift := 2 * esize - (inst.immh ++ inst.immb).toNat
    let operand := read_sfp datasize inst.Rn s
    let result := ushr_vector esize shift operand
    write_pc ((read_pc s) + 4#64) (write_sfp datasize inst.Rd result s)

@[state_simp_rules]
def exec_sli_vector (inst : Advanced_simd_shift_by_immediate_cls) (s : ArmState) : ArmState :=
  if lsb inst.immh 3 ++ inst.Q = 0b10#2 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let esize := 8 <<< highest_set_bit inst.immh
    let datasize := 64 <<< inst.Q.toNat
    let shift := (inst.immh ++ inst.immb).toNat - esize
    let operand := read_sfp datasize inst.Rn s
    let operand2 := read_sfp datasize inst.Rd s
    let result := sli_vector esize shift operand operand2
    write_pc ((read_pc s) + 4#64) (write_sfp datasize inst.Rd result s)

@[state_simp_rules]
def exec_advanced_simd_shift_by_immediate
  (inst : Advanced_simd_shift_by_immediate_cls) (s : ArmState) : ArmState :=
  if inst.immh = 0b0000#4 then
    -- `SEE(asimdimm)`: `decode_data_proc_sfp` decodes these words as modified immediate.
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else if inst.U = 1#1 ∧ inst.opcode = 0b00000#5 then
    exec_ushr_vector inst s
  else if inst.U = 1#1 ∧ inst.opcode = 0b01010#5 then
    exec_sli_vector inst s
  else
    write_err (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!") s

@[state_simp_rules]
def exec_ushr_scalar (inst : Advanced_simd_scalar_shift_by_immediate_cls) (s : ArmState) :
    ArmState :=
  if lsb inst.immh 3 ≠ 1#1 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    -- esize = datasize = 8 << 3 = 64, elements = 1
    let shift := 2 * 64 - (inst.immh ++ inst.immb).toNat
    let operand := read_sfp 64 inst.Rn s
    let result := ushr_vector 64 shift operand
    write_pc ((read_pc s) + 4#64) (write_sfp 64 inst.Rd result s)

@[state_simp_rules]
def exec_sli_scalar (inst : Advanced_simd_scalar_shift_by_immediate_cls) (s : ArmState) :
    ArmState :=
  if lsb inst.immh 3 ≠ 1#1 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    -- esize = datasize = 8 << 3 = 64, elements = 1
    let shift := (inst.immh ++ inst.immb).toNat - 64
    let operand := read_sfp 64 inst.Rn s
    let operand2 := read_sfp 64 inst.Rd s
    let result := sli_vector 64 shift operand operand2
    write_pc ((read_pc s) + 4#64) (write_sfp 64 inst.Rd result s)

@[state_simp_rules]
def exec_advanced_simd_scalar_shift_by_immediate
  (inst : Advanced_simd_scalar_shift_by_immediate_cls) (s : ArmState) : ArmState :=
  if inst.U = 1#1 ∧ inst.opcode = 0b00000#5 then
    exec_ushr_scalar inst s
  else if inst.U = 1#1 ∧ inst.opcode = 0b01010#5 then
    exec_sli_scalar inst s
  else
    write_err (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!") s

/-! ### Closed forms of the element loops -/

/-- One 64-bit element. -/
theorem binary_vector_op_64_64 (op : BitVec 64 → BitVec 64 → BitVec 64) (x y : BitVec 64) :
    binary_vector_op 64 op x y = op x y := by
  simp only [binary_vector_op, Nat.reduceDiv]
  rw [binary_vector_op_aux_of_lt (by decide : 0 < 1)]
  simp only [Nat.reduceAdd]
  rw [binary_vector_op_aux_of_not_lt (by decide : ¬ 1 < 1)]
  simp only [elem_get, elem_set, Nat.zero_mul, extractLsb'_eq_self, partInstall_eq]

/-- Two 32-bit elements of a 64-bit vector. -/
theorem binary_vector_op_32_64 (op : BitVec 32 → BitVec 32 → BitVec 32) (x y : BitVec 64) :
    binary_vector_op 32 op x y =
      op (x.extractLsb' 32 32) (y.extractLsb' 32 32) ++ op (x.extractLsb' 0 32) (y.extractLsb' 0 32) := by
  simp only [binary_vector_op, Nat.reduceDiv]
  rw [binary_vector_op_aux_of_lt (by decide : 0 < 2)]
  simp only [Nat.reduceAdd]
  rw [binary_vector_op_aux_of_lt (by decide : 1 < 2)]
  simp only [Nat.reduceAdd]
  rw [binary_vector_op_aux_of_not_lt (by decide : ¬ 2 < 2)]
  simp only [elem_get, elem_set, Nat.zero_mul, Nat.one_mul]
  generalize op (x.extractLsb' 32 32) (y.extractLsb' 32 32) = a
  generalize op (x.extractLsb' 0 32) (y.extractLsb' 0 32) = b
  have h := partInstall_partInstall (start := 0) (len₁ := 32) (len₂ := 32) (val₁ := b)
    (val₂ := a) (BitVec.zero 64)
  rw [show partInstall 0 (32 + 32) (a ++ b) (BitVec.zero 64) = a ++ b from partInstall_eq _ _]
    at h
  exact h

@[state_simp_rules]
theorem ushr_vector_64 (shift : Nat) (x : BitVec 64) : ushr_vector 64 shift x = x >>> shift := by
  simp only [ushr_vector, binary_vector_op_64_64]

@[state_simp_rules]
theorem ushr_vector_2s (shift : Nat) (x : BitVec 64) :
    ushr_vector 32 shift x = (x.extractLsb' 32 32 >>> shift) ++ (x.extractLsb' 0 32 >>> shift) := by
  simp only [ushr_vector, binary_vector_op_32_64]

@[state_simp_rules]
theorem sli_vector_64 (shift : Nat) (x y : BitVec 64) :
    sli_vector 64 shift x y = (y &&& ~~~(allOnes 64 <<< shift)) ||| (x <<< shift) := by
  simp only [sli_vector, binary_vector_op_64_64]

@[state_simp_rules]
theorem sli_vector_2s (shift : Nat) (x y : BitVec 64) :
    sli_vector 32 shift x y =
      ((y.extractLsb' 32 32 &&& ~~~(allOnes 32 <<< shift)) ||| (x.extractLsb' 32 32 <<< shift)) ++
      ((y.extractLsb' 0 32 &&& ~~~(allOnes 32 <<< shift)) ||| (x.extractLsb' 0 32 <<< shift)) := by
  simp only [sli_vector, binary_vector_op_32_64]

/-! ### Closed forms of the executions Cranelift's `fcopysign` uses

Scalar (`esize = 64`) and vector `Q = 0`, `esize = 32` (`.2s`; `immh = 01xx`). -/

theorem highest_set_bit_01xx {immh : BitVec 4} (h1 : 4 ≤ immh.toNat) (h2 : immh.toNat < 8) :
    highest_set_bit immh = 2 ∧ lsb immh 3 = 0#1 ∧ immh ≠ 0#4 := by
  have : immh = 4#4 ∨ immh = 5#4 ∨ immh = 6#4 ∨ immh = 7#4 := by bv_omega
  rcases this with rfl | rfl | rfl | rfl <;>
    exact ⟨by simp only [reduce_highest_set_bit], by decide, by decide⟩

theorem lsb_3_of_1xxx {immh : BitVec 4} (h : 8 ≤ immh.toNat) : lsb immh 3 = 1#1 := by
  have : immh = 8#4 ∨ immh = 9#4 ∨ immh = 10#4 ∨ immh = 11#4 ∨ immh = 12#4 ∨ immh = 13#4 ∨
      immh = 14#4 ∨ immh = 15#4 := by bv_omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `ushr dD, dN, #(128 - UInt(immh:immb))`. -/
theorem exec_ushr_scalar_64 (inst : Advanced_simd_scalar_shift_by_immediate_cls) (s : ArmState)
    (hU : inst.U = 1#1) (hop : inst.opcode = 0b00000#5) (hh : 8 ≤ inst.immh.toNat) :
    exec_advanced_simd_scalar_shift_by_immediate inst s =
      write_pc (read_pc s + 4#64)
        (write_sfp 64 inst.Rd
          (read_sfp 64 inst.Rn s >>> (128 - (inst.immh ++ inst.immb).toNat)) s) := by
  simp only [exec_advanced_simd_scalar_shift_by_immediate, exec_ushr_scalar, hU, hop,
    lsb_3_of_1xxx hh, ushr_vector_64, eq_self_iff_true, _root_.and_self, ne_eq,
    not_true_eq_false, ↓reduceIte, Nat.reduceMul]

/-- `sli dD, dN, #(UInt(immh:immb) - 64)`. -/
theorem exec_sli_scalar_64 (inst : Advanced_simd_scalar_shift_by_immediate_cls) (s : ArmState)
    (hU : inst.U = 1#1) (hop : inst.opcode = 0b01010#5) (hh : 8 ≤ inst.immh.toNat) :
    exec_advanced_simd_scalar_shift_by_immediate inst s =
      write_pc (read_pc s + 4#64)
        (write_sfp 64 inst.Rd
          ((read_sfp 64 inst.Rd s &&& ~~~(allOnes 64 <<< ((inst.immh ++ inst.immb).toNat - 64))) |||
            (read_sfp 64 inst.Rn s <<< ((inst.immh ++ inst.immb).toNat - 64))) s) := by
  simp only [exec_advanced_simd_scalar_shift_by_immediate, exec_sli_scalar, hU, hop,
    lsb_3_of_1xxx hh, sli_vector_64, eq_self_iff_true, _root_.and_self, ne_eq,
    not_true_eq_false, ↓reduceIte, BitVec.reduceEq, and_false, false_and, true_and]

/-- `ushr vD.2s, vN.2s, #(64 - UInt(immh:immb))`. -/
theorem exec_ushr_2s (inst : Advanced_simd_shift_by_immediate_cls) (s : ArmState)
    (hQ : inst.Q = 0#1) (hU : inst.U = 1#1) (hop : inst.opcode = 0b00000#5)
    (hh1 : 4 ≤ inst.immh.toNat) (hh2 : inst.immh.toNat < 8) :
    exec_advanced_simd_shift_by_immediate inst s =
      write_pc (read_pc s + 4#64)
        (write_sfp 64 inst.Rd
          ((read_sfp 64 inst.Rn s).extractLsb' 32 32 >>> (64 - (inst.immh ++ inst.immb).toNat) ++
            (read_sfp 64 inst.Rn s).extractLsb' 0 32 >>> (64 - (inst.immh ++ inst.immb).toNat))
          s) := by
  obtain ⟨he, hl, hz⟩ := highest_set_bit_01xx hh1 hh2
  obtain ⟨_, Q, U, _, immh, immb, opcode, _, Rn, Rd⟩ := inst
  simp only at hQ hU hop he hl hz ⊢
  subst hQ hU hop
  rw [← ushr_vector_2s]
  simp only [exec_advanced_simd_shift_by_immediate, exec_ushr_vector, hz, he, hl,
    eq_self_iff_true, _root_.and_self, ↓reduceIte, BitVec.reduceAppend, BitVec.reduceEq,
    Nat.reduceShiftLeft, Nat.reduceMul]
  rfl

/-- `sli vD.2s, vN.2s, #(UInt(immh:immb) - 32)`. -/
theorem exec_sli_2s (inst : Advanced_simd_shift_by_immediate_cls) (s : ArmState)
    (hQ : inst.Q = 0#1) (hU : inst.U = 1#1) (hop : inst.opcode = 0b01010#5)
    (hh1 : 4 ≤ inst.immh.toNat) (hh2 : inst.immh.toNat < 8) :
    exec_advanced_simd_shift_by_immediate inst s =
      write_pc (read_pc s + 4#64)
        (write_sfp 64 inst.Rd
          (((read_sfp 64 inst.Rd s).extractLsb' 32 32 &&&
                ~~~(allOnes 32 <<< ((inst.immh ++ inst.immb).toNat - 32)) |||
              (read_sfp 64 inst.Rn s).extractLsb' 32 32 <<< ((inst.immh ++ inst.immb).toNat - 32)) ++
            ((read_sfp 64 inst.Rd s).extractLsb' 0 32 &&&
                ~~~(allOnes 32 <<< ((inst.immh ++ inst.immb).toNat - 32)) |||
              (read_sfp 64 inst.Rn s).extractLsb' 0 32 <<< ((inst.immh ++ inst.immb).toNat - 32)))
          s) := by
  obtain ⟨he, hl, hz⟩ := highest_set_bit_01xx hh1 hh2
  obtain ⟨_, Q, U, _, immh, immb, opcode, _, Rn, Rd⟩ := inst
  simp only at hQ hU hop he hl hz ⊢
  subst hQ hU hop
  rw [← sli_vector_2s]
  simp only [exec_advanced_simd_shift_by_immediate, exec_sli_vector, hz, he, hl,
    eq_self_iff_true, _root_.and_self, ↓reduceIte, BitVec.reduceAppend, BitVec.reduceEq,
    Nat.reduceShiftLeft, and_false, false_and, true_and]
  rfl

end DPSFP

end Arm
