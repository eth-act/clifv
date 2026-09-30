/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import FV.Arm.Decode.DPI
import FV.Arm.Decode.DPR
import FV.Arm.Decode.BR
import FV.Arm.Decode.LDST
import FV.Arm.Decode.DPSFP
import FV.Arm.Decode.Reserved

namespace Arm


------------------------------------------------------------------------------

section Decode

open _root_.BitVec Arm.BitVec
open Std
open Std.Format

-- We do not tag any of the decode functions (e.g., decode_raw_inst or
-- its callees) with the `simp` attribute because we always expect
-- these functions to be called with a concrete instruction value. For
-- now, we can "execute" these definitions in proof using
-- "simp (config := { ground := true })".

-- Notation: We use CamelCase to define the top-level instruction
-- types, but their sub-categories' names (e.g.,
-- DataProcImmInst.Add_sub_imm) are longer and use underscores.

/--
A fully-decoded Arm instruction is represented by the ArmInst
structure.
-/
inductive ArmInst where
  | DPI   : DataProcImmInst → ArmInst
  | BR    : BranchInst      → ArmInst
  | DPR   : DataProcRegInst → ArmInst
  | DPSFP : DataProcSFPInst → ArmInst
  | LDST  : LDSTInst        → ArmInst
  /-- (FV addition) The A64 "Reserved" group: `UDF`. -/
  | RES   : ReservedInst    → ArmInst
deriving DecidableEq, Repr

instance : ToString ArmInst where toString a := toString (repr a)

def decode_data_proc_imm (i : BitVec 32) : Option ArmInst :=
  open ArmInst in
  open DataProcImmInst in
  match_bv i with
  | [sf:1, op:1, S:1, 100010, sh:1, imm12:12, Rn:5, Rd:5] =>
     DPI (Add_sub_imm {sf, op, S, sh, imm12, Rn, Rd})
  | [sf:1, opc:2, 100100, N:1, immr:6, imms:6, Rn:5, Rd:5] =>
    DPI (Logical_imm {sf, opc, N, immr, imms, Rn, Rd})
  | [op:1, immlo:2, 10000, immhi:19, Rd:5] =>
    DPI (PC_rel_addressing {op, immlo, immhi, Rd})
  | [sf:1, opc:2, 100110, N:1, immr:6, imms:6, Rn:5, Rd:5] =>
    DPI (Bitfield {sf, opc, N, immr, imms, Rn, Rd})
  | [sf:1, opc:2, 100101, hw:2, imm16:16, Rd:5] =>
    DPI (Move_wide_imm {sf, opc, hw, imm16, Rd})
  -- (FV addition) Extract.
  | [sf:1, op21:2, 100111, N:1, o0:1, Rm:5, imms:6, Rn:5, Rd:5] =>
    DPI (Extract {sf, op21, N, o0, Rm, imms, Rn, Rd})
  | _ => none

def decode_branch (i : BitVec 32) : Option ArmInst :=
  open ArmInst in
  open BranchInst in
  match_bv i with
  | [sf:1, 011010, op:1, imm19:19, Rt:5] =>
    BR (Compare_branch {sf, op, imm19, Rt})
  | [op:1, 00101, imm26:26] =>
    BR (Uncond_branch_imm {op, imm26})
  | [1101011, opc:4, op2:5, op3:6, Rn:5, op4:5] =>
    BR (Uncond_branch_reg {opc, op2, op3, Rn, op4})
  | [01010100, imm19:19, o0:1, cond:4] =>
    BR (Cond_branch_imm {imm19, o0, cond})
  | [11010101000000110010, CRm:4, op2:3, 11111] =>
    BR (Hints {CRm, op2})
  -- (FV addition) Barriers: DMB (the backend emits only `dmb ish`).
  | [1101010100000011, 00, 11, CRm:4, op2:3, 11111] =>
    BR (Barrier {CRm, op2})
  -- (FV addition) Test and branch (immediate).
  | [b5:1, 011011, op:1, b40:5, imm14:14, Rt:5] =>
    BR (Test_branch {b5, op, b40, imm14, Rt})
  | _ => none

def decode_data_proc_reg (i : BitVec 32) : Option ArmInst :=
  open ArmInst in
  open DataProcRegInst in
  match_bv i with
  | [sf:1, op:1, S:1, 11010000, Rm:5, 000000, Rn:5, Rd:5] =>
    DPR (Add_sub_carry {sf, op, S, Rm, Rn, Rd})
  | [sf:1, op:1, S:1, 01011, shift:2, 0, Rm:5, imm6:6 , Rn:5, Rd:5] =>
    DPR (Add_sub_shifted_reg {sf, op, S, shift, Rm, imm6, Rn, Rd})
  -- (FV addition) Add/subtract (extended register).
  | [sf:1, op:1, S:1, 01011, opt:2, 1, Rm:5, option:3, imm3:3, Rn:5, Rd:5] =>
    DPR (Add_sub_ext_reg {sf, op, S, opt, Rm, option, imm3, Rn, Rd})
  -- (FV addition) Conditional compare (immediate) / (register).
  | [sf:1, op:1, S:1, 11010010, imm5:5, cond:4, 1, o2:1, Rn:5, o3:1, nzcv:4] =>
    DPR (Conditional_compare_imm {sf, op, S, imm5, cond, o2, Rn, o3, nzcv})
  | [sf:1, op:1, S:1, 11010010, Rm:5, cond:4, 0, o2:1, Rn:5, o3:1, nzcv:4] =>
    DPR (Conditional_compare_reg {sf, op, S, Rm, cond, o2, Rn, o3, nzcv})
  | [sf:1, op:1, S:1, 11010100, Rm:5, cond:4, op2:2, Rn:5, Rd:5] =>
    DPR (Conditional_select {sf, op, S, Rm, cond, op2, Rn, Rd})
  | [sf:1, 1, S:1, 11010110, opcode2:5, opcode:6, Rn:5, Rd:5] =>
    DPR (Data_processing_one_source {sf, S, opcode2, opcode, Rn, Rd})
  | [sf:1, 0, S:1, 11010110, Rm:5, opcode:6, Rn:5, Rd:5] =>
    DPR (Data_processing_two_source {sf, S, Rm, opcode, Rn, Rd})
  | [sf:1, opc:2, 01010, shift:2, N:1, Rm:5, imm6:6, Rn:5, Rd:5] =>
    DPR (Logical_shifted_reg {sf, opc, shift, N, Rm, imm6, Rn, Rd})
  | [sf:1, op54:2, 11011, op31:3, Rm:5, o0:1, Ra:5, Rn:5, Rd:5] =>
    DPR (Data_processing_three_source {sf, op54, op31, Rm, o0, Ra, Rn, Rd})
  | _ => none

def decode_data_proc_sfp (i : BitVec 32) : Option ArmInst :=
  open ArmInst in
  open DataProcSFPInst in
  match_bv i with
  | [0, Q:1, U:1, 01110, size:2, 10000, opcode:5, 10, Rn:5, Rd:5] =>
    DPSFP (Advanced_simd_two_reg_misc {Q, U, size, opcode, Rn, Rd})
  | [0, Q:1, op:1, 01110000, imm5:5, 0, imm4:4, 1, Rn:5, Rd:5] =>
    DPSFP (Advanced_simd_copy {Q, op, imm5, imm4, Rn, Rd})
  | [0, Q:1, U:1, 01110, size:2, 1, Rm:5, opcode:5, 1, Rn:5, Rd:5] =>
    DPSFP (Advanced_simd_three_same {Q, U, size, Rm, opcode, Rn, Rd})
  | [sf:1, 0, S:1, 11110, ftype:2, 1, rmode:2, opcode:3, 000000, Rn:5, Rd:5] =>
    DPSFP (Conversion_between_FP_and_Int {sf, S, ftype, rmode, opcode, Rn, Rd})
  -- (FV addition) Advanced SIMD across lanes.
  | [0, Q:1, U:1, 01110, size:2, 11000, opcode:5, 10, Rn:5, Rd:5] =>
    DPSFP (Advanced_simd_across_lanes {Q, U, size, opcode, Rn, Rd})
  | _ => none

def decode_ldst_inst (i : BitVec 32) : Option ArmInst :=
  open ArmInst in
  open LDSTInst in
  match_bv i with
  | [size:2, 111, V:1, 00, opc:2, 0, imm9:9, 01, Rn:5, Rt:5] =>
    LDST (Reg_imm_post_indexed {size, V, opc, imm9, Rn, Rt})
  | [size:2, 111, V:1, 01, opc:2, imm12:12, Rn:5, Rt:5] =>
    LDST (Reg_unsigned_imm {size, V, opc, imm12, Rn, Rt})
  | [size:2, 111, VR:1, 00, opc:2, 0, imm9:9, 00, Rn:5, Rt:5] =>
    LDST (Reg_unscaled_imm {size, VR, opc, imm9, Rn, Rt})
  | [opc:2, 101, V:1, 011, L:1, imm7:7, Rt2:5, Rn:5, Rt:5] =>
    LDST (Reg_pair_pre_indexed {opc, V, L, imm7, Rt2, Rn, Rt})
  | [opc:2, 101, V:1, 001, L:1, imm7:7, Rt2:5, Rn:5, Rt:5] =>
    LDST (Reg_pair_post_indexed {opc, V, L, imm7, Rt2, Rn, Rt})
  | [opc:2, 101, V:1, 010, L:1, imm7:7, Rt2:5, Rn:5, Rt:5] =>
    LDST (Reg_pair_signed_offset {opc, V, L, imm7, Rt2, Rn, Rt})
  -- (FV addition) Load/store register (immediate pre-indexed) / (register offset).
  | [size:2, 111, V:1, 00, opc:2, 0, imm9:9, 11, Rn:5, Rt:5] =>
    LDST (Reg_imm_pre_indexed {size, V, opc, imm9, Rn, Rt})
  | [size:2, 111, V:1, 00, opc:2, 1, Rm:5, option:3, S:1, 10, Rn:5, Rt:5] =>
    LDST (Reg_reg_offset {size, V, opc, Rm, option, S, Rn, Rt})
  -- (FV addition) Load/store exclusive / acquire-release: LDXR/LDAXR/STXR/STLXR/LDAR/STLR.
  | [size:2, 001000, o2:1, L:1, 0, Rs:5, o0:1, 11111, Rn:5, Rt:5] =>
    LDST (Reg_exclusive {size, ord := o2, L, Rs, o0, Rn, Rt})
  | _ => none

/-- (FV addition) Decode the A64 "Reserved" group (`op0 = 0`, `op1 = 0000`). -/
def decode_reserved (i : BitVec 32) : Option ArmInst :=
  open ArmInst in
  open ReservedInst in
  match_bv i with
  | [0000000000000000, imm16:16] =>
    RES (Udf {imm16})
  | _ => none

-- Decode a 32-bit instruction `i`.
def decode_raw_inst (i : BitVec 32) : Option ArmInst :=
  open ArmInst in
  match_bv i with
  | [op0:1, _x:2, op1:4, _y:25] =>
    match op0, op1 with
    | 0#1, 0b0000#4 => decode_reserved i
    | _, 0b1000#4 | _, 0b1001#4 => decode_data_proc_imm i
    | _, 0b1010#4 | _, 0b1011#4 => decode_branch i
    | _, 0b1101#4 | _, 0b0101#4 => decode_data_proc_reg i
    | _, 0b0111#4 | _, 0b1111#4 => decode_data_proc_sfp i
    | _, 0b0100#4 | _, 0b1100#4 | _, 0b0110#4 | _, 0b1110#4 => decode_ldst_inst i
    | _, _ => none
  | _ => none

------------------------------------------------------------------------

-- add x1, x1, 1
example : decode_raw_inst 0x91000421#32 =
          (ArmInst.DPI (DataProcImmInst.Add_sub_imm
          {sf := 1#1, op := 0#1, S := 0#1, sh := 0#1,
            imm12 := 1#12, Rn := 1#5, Rd := 1#5})) := rfl

-- adc x1, x1, x0
example : decode_raw_inst 0b00011010000000000000000000100001#32 =
          (ArmInst.DPR (DataProcRegInst.Add_sub_carry
               { sf := 0#1, op := 0#1, S := 0#1, Rm := 0#5,
                 Rn := 1#5, Rd := 1#5 })) := rfl

-- ldr	q16, [x0], #16
example : decode_raw_inst 0x3cc10410#32 =
          (ArmInst.LDST (LDSTInst.Reg_imm_post_indexed
               { size := 0x0#2, V := 0x1#1, opc := 0x3#2, imm9 := 0x010#9,
                 Rn := 0x00#5, Rt := 0x10#5 })) := rfl

-- stp	x29, x30, [sp, #-16]!
example : decode_raw_inst 0xa9bf7bfd#32 =
          (ArmInst.LDST (LDSTInst.Reg_pair_pre_indexed
               { opc := 0x2#2, V := 0x0#1, L := 0x0#1, imm7 := 0x7e#7,
                 Rt2 := 0x1e#5, Rn := 0x1f#5, Rt := 0x1d#5 })) := rfl

-- add	v24.2d, v24.2d, v16.2d
example : decode_raw_inst 0x4ef08718#32 =
  (ArmInst.DPSFP (DataProcSFPInst.Advanced_simd_three_same
       { Q := 0x1#1, U := 0x0#1, size := 0x3#2, Rm := 0x10#5,
         opcode := 0x10#5, Rn := 0x18#5, Rd := 0x18#5 })) := rfl

-- adrp x3, ...
example : decode_raw_inst 0xd0000463#32 =
          (ArmInst.DPI (DataProcImmInst.PC_rel_addressing
               { op := 0x1#1, immlo := 0x2#2, immhi := 0x00023#19,
                 Rd := 0x03#5 })) := rfl

-- csel	x1, x1, x4, ne
example : decode_raw_inst 0x9a841021#32 =
          (ArmInst.DPR (DataProcRegInst.Conditional_select
               { sf := 0x1#1, op := 0x0#1, S := 0x0#1, Rm := 0x04#5,
                 cond := 0x1#4, op2 := 0x0#2, Rn := 0x01#5,
                 Rd := 0x01#5 })) := rfl

-- b ...
example : decode_raw_inst 0x14000001#32 =
          (ArmInst.BR (BranchInst.Uncond_branch_imm
               { op := 0x0#1, imm26 := 0x0000001#26 })) := rfl

-- b.le ...
example : decode_raw_inst 0x5400000d#32 =
          (ArmInst.BR (BranchInst.Cond_branch_imm
               { imm19 := 0x00000#19, o0 := 0, cond := 0xd#4})) := rfl

-- ret
example : decode_raw_inst 0xd65f03c0#32 =
          (ArmInst.BR (BranchInst.Uncond_branch_reg
               { opc := 0x2#4, op2 := 0x1f#5, op3 := 0x00#6,
                 Rn := 0x1e#5, op4 := 0x00#5 })) := rfl

-- cbnz	x2, ...
example : decode_raw_inst 0xb5ffc382#32 =
          (ArmInst.BR (BranchInst.Compare_branch
               { sf := 0x1#1, op := 0x1#1, imm19 := 0x7fe1c#19,
                 Rt := 0x02#5 })) := rfl

-- mov	x29, sp
example : decode_raw_inst 0x910003fd#32 =
          (ArmInst.DPI (DataProcImmInst.Add_sub_imm
               { sf := 0x1#1, op := 0x0#1, S := 0x0#1, sh := 0x0#1,
                 imm12 := 0x000#12, Rn := 0x1f#5, Rd := 0x1d#5 })) := rfl

-- ldr	q0, [x4]
example : decode_raw_inst 0x3dc00080#32 =
          (ArmInst.LDST (LDSTInst.Reg_unsigned_imm
               { size := 0x0#2, V := 0x1#1, opc := 0x3#2,
                 imm12 := 0x000#12, Rn := 0x04#5, Rt := 0x00#5 })) := rfl

-- str	q4, [x2], #16
example : decode_raw_inst 0x3c810444#32 =
          (ArmInst.LDST (LDSTInst.Reg_imm_post_indexed
               { size := 0x0#2, V := 0x1#1, opc := 0x2#2, imm9 := 0x010#9,
                 Rn := 0x02#5, Rt := 0x04#5 })) := by
        rfl

-- rev64 v0.16b, v0.16b
example : decode_raw_inst 0x4e200800#32 =
          (ArmInst.DPSFP
               (DataProcSFPInst.Advanced_simd_two_reg_misc
                 { Q := 0x1#1, U := 0x0#1, size := 0x0#2, opcode := 0x00#5,
                   Rn := 0x00#5, Rd := 0x00#5 })) := rfl

-- mov	x28, v0.d[0]
example : decode_raw_inst 0x4e083c1c#32 =
          ArmInst.DPSFP (DataProcSFPInst.Advanced_simd_copy
              { Q := 0x1#1, op := 0x0#1, imm5 := 0x08#5,
                imm4 := 0x7#4, Rn := 0x00#5, Rd := 0x1c#5 }) := rfl

-- lsr w0, w0, #1
example : decode_raw_inst 0x53017c00#32 =
          (ArmInst.DPI
            (DataProcImmInst.Bitfield
              { sf := 0x0#1,
                opc := 0x2#2,
                _fixed := 0x26#6,
                N := 0x0#1,
                immr := 0x01#6,
                imms := 0x1f#6,
                Rn := 0x00#5,
                Rd := 0x00#5 })) := rfl

-- ands x30, x3, x17, asr #35
example : decode_raw_inst 0xea918c7e#32 =
          (ArmInst.DPR (DataProcRegInst.Logical_shifted_reg
          { sf := 0x1#1,
            opc := 0x3#2,
            _fixed := 0x0a#5,
            shift := 0x2#2,
            N := 0x0#1,
            Rm := 0x11#5,
            imm6 := 0x23#6,
            Rn := 0x03#5,
            Rd := 0x1e#5})) := rfl

-- eor x15, x28, #0xffffc00000000001
example : decode_raw_inst 0xd2524b8f#32 =
          (ArmInst.DPI (DataProcImmInst.Logical_imm
          { sf := 0x1#1,
            opc := 0x2#2,
            _fixed := 0x24#6,
            N := 0x1#1,
            immr := 0x12#6,
            imms := 0x12#6,
            Rn := 0x1c#5,
            Rd := 0x0f#5 })) := rfl

-- sub x9, x27, x15, lsl #55
example : decode_raw_inst 0xcb0fdf69 =
          (ArmInst.DPR (DataProcRegInst.Add_sub_shifted_reg
          { sf := 0x1#1,
            op := 0x1#1,
            S := 0x0#1,
            _fixed1 := 0x0b#5,
            shift := 0x0#2,
            _fixed2 := 0x0#1,
            Rm := 0x0f#5,
            imm6 := 0x37#6,
            Rn := 0x1b#5,
            Rd := 0x09#5 })) := rfl

-- mov v10.h[0] v17.h[6]
example : decode_raw_inst 0x6e026e2a =
          (ArmInst.DPSFP
            (DataProcSFPInst.Advanced_simd_copy
          { _fixed1 := 0x0#1,
            Q := 0x1#1,
            op := 0x1#1,
            _fixed2 := 0x70#8,
            imm5 := 0x02#5,
            _fixed3 := 0x0#1,
            imm4 := 0xd#4,
            _fixed4 := 0x1#1,
            Rn := 0x11#5,
            Rd := 0x0a#5 })) := rfl

-- fmov v25.d[1], x5
example : decode_raw_inst 0x9eaf00b9 =
          (ArmInst.DPSFP
            (DataProcSFPInst.Conversion_between_FP_and_Int
            { sf := 0x1#1,
              _fixed1 := 0x0#1,
              S := 0x0#1,
              _fixed2 := 0x1e#5,
              ftype := 0x2#2,
              _fixed3 := 0x1#1,
              rmode := 0x1#2,
              opcode := 0x7#3,
              _fixed4 := 0x00#6,
              Rn := 0x05#5,
              Rd := 0x19#5 })) := rfl

-- rev x0, x25
example : decode_raw_inst 0xdac00f20 =
          (ArmInst.DPR
            (DataProcRegInst.Data_processing_one_source
            { sf := 0x1#1,
              _fixed1 := 0x1#1,
              S := 0x0#1,
              _fixed2 := 0xd6#8,
              opcode2 := 0x00#5,
              opcode := 0x03#6,
              Rn := 0x19#5,
              Rd := 0x00#5 })) := rfl

-- (FV) `0x00000000` is `udf #0` (upstream decoded it as `none` before UDF was added).
example : decode_raw_inst 0x00000000#32 = ArmInst.RES (ReservedInst.Udf { imm16 := 0#16 }) :=
  rfl

-- udf #0xc11f (Cranelift's trap instruction)
example : decode_raw_inst 0x0000c11f#32 =
          ArmInst.RES (ReservedInst.Udf { imm16 := 0xc11f#16 }) := rfl

-- Unallocated (op0 = 0, op1 = 0001)
example : decode_raw_inst 0x02000000#32 = none := rfl

-- ror w0, w0, #29 (= extr w0, w0, w0, #29)
example : decode_raw_inst 0x13807400#32 =
          ArmInst.DPI (DataProcImmInst.Extract
            { sf := 0#1, op21 := 0#2, N := 0#1, o0 := 0#1, Rm := 0#5, imms := 29#6,
              Rn := 0#5, Rd := 0#5 }) := rfl

-- tbnz x0, #63, #12
example : decode_raw_inst 0xb7f80060#32 =
          ArmInst.BR (BranchInst.Test_branch
            { b5 := 1#1, op := 1#1, b40 := 0x1f#5, imm14 := 3#14, Rt := 0#5 }) := rfl

-- add x0, x0, w1, sxtb
example : decode_raw_inst 0x8b218000#32 =
          ArmInst.DPR (DataProcRegInst.Add_sub_ext_reg
            { sf := 1#1, op := 0#1, S := 0#1, opt := 0#2, Rm := 1#5, option := 0b100#3,
              imm3 := 0#3, Rn := 0#5, Rd := 0#5 }) := rfl

-- ccmp x0, #1, #0, eq
example : decode_raw_inst 0xfa410800#32 =
          ArmInst.DPR (DataProcRegInst.Conditional_compare_imm
            { sf := 1#1, op := 1#1, S := 1#1, imm5 := 1#5, cond := 0#4, o2 := 0#1,
              Rn := 0#5, o3 := 0#1, nzcv := 0#4 }) := rfl

-- ldrsw x10, [x9, w10, uxtw #2]
example : decode_raw_inst 0xb8aa592a#32 =
          ArmInst.LDST (LDSTInst.Reg_reg_offset
            { size := 2#2, V := 0#1, opc := 2#2, Rm := 10#5, option := 0b010#3, S := 1#1,
              Rn := 9#5, Rt := 10#5 }) := rfl

-- str x21, [sp, #-16]!
example : decode_raw_inst 0xf81f0ff5#32 =
          ArmInst.LDST (LDSTInst.Reg_imm_pre_indexed
            { size := 3#2, V := 0#1, opc := 0#2, imm9 := 0x1f0#9, Rn := 31#5, Rt := 21#5 }) :=
  rfl

-- addv b6, v4.8b
example : decode_raw_inst 0x0e31b886#32 =
          ArmInst.DPSFP (DataProcSFPInst.Advanced_simd_across_lanes
            { Q := 0#1, U := 0#1, size := 0#2, opcode := 0b11011#5, Rn := 4#5, Rd := 6#5 }) :=
  rfl

end Decode

end Arm
