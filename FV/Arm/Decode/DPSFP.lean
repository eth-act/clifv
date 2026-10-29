/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
module

import FV.Arm.BitVec

public section

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

/-- (FV addition) Advanced SIMD across lanes (`ADDV`, ...). -/
structure Advanced_simd_across_lanes_cls where
  _fixed1 : BitVec 1 := 0b0#1      -- [31:31]
  Q       : BitVec 1               -- [30:30]
  U       : BitVec 1               -- [29:29]
  _fixed2 : BitVec 5 := 0b01110#5  -- [28:24]
  size    : BitVec 2               -- [23:22]
  _fixed3 : BitVec 5 := 0b11000#5  -- [21:17]
  opcode  : BitVec 5               -- [16:12]
  _fixed4 : BitVec 2 := 0b10#2     -- [11:10]
  Rn      : BitVec 5               --   [9:5]
  Rd      : BitVec 5               --   [4:0]
deriving DecidableEq, Repr

instance : ToString Advanced_simd_across_lanes_cls where toString a := toString (repr a)

/-- (FV addition) Floating-point data-processing (1 source): FMOV (register), FABS, FNEG, FSQRT,
FCVT, FRINT* (Arm ARM C4.1 "Data Processing -- Scalar Floating-Point and Advanced SIMD"). -/
structure FP_data_processing_one_source_cls where
  M       : BitVec 1               -- [31:31]
  _fixed1 : BitVec 1 := 0b0#1      -- [30:30]
  S       : BitVec 1               -- [29:29]
  _fixed2 : BitVec 5 := 0b11110#5  -- [28:24]
  ftype   : BitVec 2               -- [23:22]
  _fixed3 : BitVec 1 := 0b1#1      -- [21:21]
  opcode  : BitVec 6               -- [20:15]
  _fixed4 : BitVec 5 := 0b10000#5  -- [14:10]
  Rn      : BitVec 5               --   [9:5]
  Rd      : BitVec 5               --   [4:0]
deriving DecidableEq, Repr

instance : ToString FP_data_processing_one_source_cls where toString a := toString (repr a)

/-- (FV addition) Floating-point immediate: FMOV (scalar, immediate). -/
structure FP_immediate_cls where
  M       : BitVec 1               -- [31:31]
  _fixed1 : BitVec 1 := 0b0#1      -- [30:30]
  S       : BitVec 1               -- [29:29]
  _fixed2 : BitVec 5 := 0b11110#5  -- [28:24]
  ftype   : BitVec 2               -- [23:22]
  _fixed3 : BitVec 1 := 0b1#1      -- [21:21]
  imm8    : BitVec 8               -- [20:13]
  _fixed4 : BitVec 3 := 0b100#3    -- [12:10]
  imm5    : BitVec 5               --   [9:5]
  Rd      : BitVec 5               --   [4:0]
deriving DecidableEq, Repr

instance : ToString FP_immediate_cls where toString a := toString (repr a)

/-- (FV addition) Floating-point conditional select: FCSEL. -/
structure FP_conditional_select_cls where
  M       : BitVec 1               -- [31:31]
  _fixed1 : BitVec 1 := 0b0#1      -- [30:30]
  S       : BitVec 1               -- [29:29]
  _fixed2 : BitVec 5 := 0b11110#5  -- [28:24]
  ftype   : BitVec 2               -- [23:22]
  _fixed3 : BitVec 1 := 0b1#1      -- [21:21]
  Rm      : BitVec 5               -- [20:16]
  cond    : BitVec 4               -- [15:12]
  _fixed4 : BitVec 2 := 0b11#2     -- [11:10]
  Rn      : BitVec 5               --   [9:5]
  Rd      : BitVec 5               --   [4:0]
deriving DecidableEq, Repr

instance : ToString FP_conditional_select_cls where toString a := toString (repr a)

/-- (FV addition, ported from LNSym) Advanced SIMD modified immediate: MOVI, MVNI, ORR, BIC
(vector, immediate), FMOV (vector, immediate). -/
structure Advanced_simd_modified_immediate_cls where
  _fixed1 : BitVec 1 := 0b0#1            -- [31:31]
  Q       : BitVec 1                     -- [30:30]
  op      : BitVec 1                     -- [29:29]
  _fixed2 : BitVec 10 := 0b0111100000#10 -- [28:19]
  a       : BitVec 1                     -- [18:18]
  b       : BitVec 1                     -- [17:17]
  c       : BitVec 1                     -- [16:16]
  cmode   : BitVec 4                     -- [15:12]
  o2      : BitVec 1                     -- [11:11]
  _fixed3 : BitVec 1 := 0b1#1            -- [10:10]
  d       : BitVec 1                     --   [9:9]
  e       : BitVec 1                     --   [8:8]
  f       : BitVec 1                     --   [7:7]
  g       : BitVec 1                     --   [6:6]
  h       : BitVec 1                     --   [5:5]
  Rd      : BitVec 5                     --   [4:0]
deriving DecidableEq, Repr

@[expose] instance : ToString Advanced_simd_modified_immediate_cls where toString a := toString (repr a)

/-- (FV addition) Floating-point data-processing (2 source): FMUL, FDIV, FADD, FSUB, FMAX,
FMIN, FMAXNM, FMINNM, FNMUL (scalar). -/
structure FP_data_processing_two_source_cls where
  M       : BitVec 1               -- [31:31]
  _fixed1 : BitVec 1 := 0b0#1      -- [30:30]
  S       : BitVec 1               -- [29:29]
  _fixed2 : BitVec 5 := 0b11110#5  -- [28:24]
  ftype   : BitVec 2               -- [23:22]
  _fixed3 : BitVec 1 := 0b1#1      -- [21:21]
  Rm      : BitVec 5               -- [20:16]
  opcode  : BitVec 4               -- [15:12]
  _fixed4 : BitVec 2 := 0b10#2     -- [11:10]
  Rn      : BitVec 5               --   [9:5]
  Rd      : BitVec 5               --   [4:0]
deriving DecidableEq, Repr

instance : ToString FP_data_processing_two_source_cls where toString a := toString (repr a)

/-- (FV addition) Floating-point data-processing (3 source): FMADD, FMSUB, FNMADD, FNMSUB. -/
structure FP_data_processing_three_source_cls where
  M       : BitVec 1               -- [31:31]
  _fixed1 : BitVec 1 := 0b0#1      -- [30:30]
  S       : BitVec 1               -- [29:29]
  _fixed2 : BitVec 5 := 0b11111#5  -- [28:24]
  ftype   : BitVec 2               -- [23:22]
  o1      : BitVec 1               -- [21:21]
  Rm      : BitVec 5               -- [20:16]
  o0      : BitVec 1               -- [15:15]
  Ra      : BitVec 5               -- [14:10]
  Rn      : BitVec 5               --   [9:5]
  Rd      : BitVec 5               --   [4:0]
deriving DecidableEq, Repr

instance : ToString FP_data_processing_three_source_cls where toString a := toString (repr a)

/-- (FV addition) Floating-point compare: FCMP, FCMPE (register and `#0.0`). -/
structure FP_compare_cls where
  M       : BitVec 1               -- [31:31]
  _fixed1 : BitVec 1 := 0b0#1      -- [30:30]
  S       : BitVec 1               -- [29:29]
  _fixed2 : BitVec 5 := 0b11110#5  -- [28:24]
  ftype   : BitVec 2               -- [23:22]
  _fixed3 : BitVec 1 := 0b1#1      -- [21:21]
  Rm      : BitVec 5               -- [20:16]
  op      : BitVec 2               -- [15:14]
  _fixed4 : BitVec 4 := 0b1000#4   -- [13:10]
  Rn      : BitVec 5               --   [9:5]
  opcode2 : BitVec 5               --   [4:0]
deriving DecidableEq, Repr

instance : ToString FP_compare_cls where toString a := toString (repr a)

inductive DataProcSFPInst where
  | Advanced_simd_two_reg_misc :
    Advanced_simd_two_reg_misc_cls → DataProcSFPInst
  | Advanced_simd_copy :
    Advanced_simd_copy_cls → DataProcSFPInst
  | Advanced_simd_three_same :
    Advanced_simd_three_same_cls → DataProcSFPInst
  | Conversion_between_FP_and_Int :
    Conversion_between_FP_and_Int_cls → DataProcSFPInst
  | Advanced_simd_across_lanes :
    Advanced_simd_across_lanes_cls → DataProcSFPInst
  | FP_data_processing_one_source :
    FP_data_processing_one_source_cls → DataProcSFPInst
  | FP_immediate :
    FP_immediate_cls → DataProcSFPInst
  | FP_conditional_select :
    FP_conditional_select_cls → DataProcSFPInst
  | Advanced_simd_modified_immediate :
    Advanced_simd_modified_immediate_cls → DataProcSFPInst
  | FP_data_processing_two_source :
    FP_data_processing_two_source_cls → DataProcSFPInst
  | FP_data_processing_three_source :
    FP_data_processing_three_source_cls → DataProcSFPInst
  | FP_compare :
    FP_compare_cls → DataProcSFPInst
deriving DecidableEq, Repr

instance : ToString DataProcSFPInst where toString a := toString (repr a)

end Decode

end Arm
