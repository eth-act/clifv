/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
import FV.Arm.BitVec

namespace Arm


------------------------------------------------------------------------------

section Decode

open _root_.BitVec Arm.BitVec

-- Data Processing (SIMD and FP) Instructions --

structure Advanced_simd_two_reg_misc_cls where
  _fixed1 : BitVec 1 := 0b0#1      -- [31:31]
  Q       : BitVec 1               -- [30:30]
  U       : BitVec 1               -- [29:29]
  _fixed2 : BitVec 5 := 0b01110#5  -- [28:24]
  size    : BitVec 2               -- [23:22]
  _fixed3 : BitVec 5 := 0b10000#5  -- [21:17]
  opcode  : BitVec 5               -- [16:12]
  _fixed4 : BitVec 2 := 0b10#2     -- [11:10]
  Rn      : BitVec 5               --   [9:5]
  Rd      : BitVec 5               --   [4:0]
deriving DecidableEq, Repr

instance : ToString Advanced_simd_two_reg_misc_cls where toString a := toString (repr a)

def Advanced_simd_two_reg_misc_cls.toBitVec32 (x : Advanced_simd_two_reg_misc_cls) : BitVec 32 :=
  x._fixed1 ++ x.Q ++ x.U ++ x._fixed2 ++ x.size ++ x._fixed3 ++ x.opcode ++ x._fixed4 ++ x.Rn ++ x.Rd

structure Advanced_simd_copy_cls where
  _fixed1 : BitVec 1 := 0b0#1        -- [31:31]
  Q       : BitVec 1                 -- [30:30]
  op      : BitVec 1                 -- [29:29]
  _fixed2 : BitVec 8 := 0b01110000#8 -- [28:21]
  imm5    : BitVec 5                 -- [20:16]
  _fixed3 : BitVec 1 := 0b0#1        -- [15:15]
  imm4    : BitVec 4                 -- [14:11]
  _fixed4 : BitVec 1 := 0b1#1        -- [10:10]
  Rn      : BitVec 5                 --   [9:5]
  Rd      : BitVec 5                 --   [4:0]
deriving DecidableEq, Repr

instance : ToString Advanced_simd_copy_cls where toString a := toString (repr a)

def Advanced_simd_copy_cls.toBitVec32 (x : Advanced_simd_copy_cls) : BitVec 32 :=
  x._fixed1 ++ x.Q ++ x.op ++ x._fixed2 ++ x.imm5 ++ x._fixed3 ++ x.imm4 ++ x._fixed4 ++ x.Rn ++ x.Rd

structure Advanced_simd_three_same_cls where
  _fixed1 : BitVec 1 := 0b0#1      -- [31:31]
  Q       : BitVec 1               -- [30:30]
  U       : BitVec 1               -- [29:29]
  _fixed2 : BitVec 5 := 0b01110#5  -- [28:24]
  size    : BitVec 2               -- [23:22]
  _fixed3 : BitVec 1 := 0b1#1      -- [21:21]
  Rm      : BitVec 5               -- [20:16]
  opcode  : BitVec 5               -- [15:11]
  _fixed4 : BitVec 1 := 0b1#1      -- [10:10]
  Rn      : BitVec 5               --   [9:5]
  Rd      : BitVec 5               --   [4:0]
deriving DecidableEq, Repr

instance : ToString Advanced_simd_three_same_cls where toString a := toString (repr a)

def Advanced_simd_three_same_cls.toBitVec32 (x : Advanced_simd_three_same_cls) : BitVec 32 :=
  x._fixed1 ++ x.Q ++ x.U ++ x._fixed2 ++ x.size ++ x._fixed3 ++ x.Rm ++ x.opcode ++ x._fixed4 ++ x.Rn ++ x.Rd

structure Conversion_between_FP_and_Int_cls where
  sf      : BitVec 1               -- [31:31]
  _fixed1 : BitVec 1 := 0b0#1      -- [30:30]
  S       : BitVec 1               -- [29:29]
  _fixed2 : BitVec 5 := 0b11110#5  -- [28:24]
  ftype   : BitVec 2               -- [23:22]
  _fixed3 : BitVec 1 := 0b1#1      -- [21:21]
  rmode   : BitVec 2               -- [20:19]
  opcode  : BitVec 3               -- [18:16]
  _fixed4 : BitVec 6 := 0b000000#6 -- [15:10]
  Rn      : BitVec 5               -- [9:5]
  Rd      : BitVec 5               -- [4:0]
deriving DecidableEq, Repr

instance : ToString Conversion_between_FP_and_Int_cls where toString a := toString (repr a)

def Conversion_between_FP_and_Int_cls.toBitVec32 (x : Conversion_between_FP_and_Int_cls) : BitVec 32 :=
  x.sf ++ x._fixed1 ++ x.S ++ x._fixed2 ++ x.ftype ++ x._fixed3 ++ x.rmode ++ x.opcode ++ x._fixed4 ++ x.Rn ++ x.Rd

inductive DataProcSFPInst where
  | Advanced_simd_two_reg_misc :
    Advanced_simd_two_reg_misc_cls → DataProcSFPInst
  | Advanced_simd_copy :
    Advanced_simd_copy_cls → DataProcSFPInst
  | Advanced_simd_three_same :
    Advanced_simd_three_same_cls → DataProcSFPInst
  | Conversion_between_FP_and_Int :
    Conversion_between_FP_and_Int_cls → DataProcSFPInst
deriving DecidableEq, Repr

instance : ToString DataProcSFPInst where toString a := toString (repr a)

end Decode

end Arm
