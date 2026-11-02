/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Yan Peng
-/
import FV.Arm.BitVec

namespace Arm


------------------------------------------------------------------------------

section Decode

open _root_.BitVec Arm.BitVec

-- Branches, Exception Generating and System Instructions

structure Compare_branch_cls where
  sf     : BitVec 1               -- [31:31]
  _fixed : BitVec 5 := 0b011010#5 -- [30:25]
  op     : BitVec 1               -- [24:24]
  imm19  : BitVec 19              -- [23:5]
  Rt     : BitVec 5               --  [4:0]
deriving DecidableEq, Repr

instance : ToString Compare_branch_cls where toString a := toString (repr a)

structure Uncond_branch_imm_cls where
  op     : BitVec 1              -- [31:31]
  _fixed : BitVec 5 := 0b00101#5 -- [30:26]
  imm26  : BitVec 26             --  [25:0]
deriving DecidableEq, Repr

instance : ToString Uncond_branch_imm_cls where toString a := toString (repr a)

structure Uncond_branch_reg_cls where
  _fixed : BitVec 7 := 0b1101011#7 -- [31:25]
  opc    : BitVec 4                -- [24:21]
  op2    : BitVec 5                -- [20:16]
  op3    : BitVec 6                -- [15:10]
  Rn     : BitVec 5                --   [9:5]
  -- This field is indeed called
  -- op4 in the Arm manual; note
  -- that the width is 5 bits.
  op4    : BitVec 5                --  [4:0]
deriving DecidableEq, Repr

instance : ToString Uncond_branch_reg_cls where toString a := toString (repr a)

structure Cond_branch_imm_cls where
  _fixed : BitVec 8 := 0b01010100#8 -- [31:24]
  imm19  : BitVec 19                -- [23:5]
  o0     : BitVec 1                 -- [4:4]
  cond   : BitVec 4                 -- [3:0]
deriving DecidableEq, Repr

instance : ToString Cond_branch_imm_cls where toString a := toString (repr a)

structure Hints_cls where
  _fixed1 : BitVec 20 := 0b11010101000000110010#20 -- [31:12]
  CRm     : BitVec 4                               -- [11:8]
  op2     : BitVec 3                               -- [7:5]
  _fixed2 : BitVec 5 := 0b11111#5                  -- [4:0]
deriving DecidableEq, Repr

instance : ToString Hints_cls where toString a := toString (repr a)

def Hints_cls.toBitVec32 (x : Hints_cls) : BitVec 32 :=
  x._fixed1 ++ x.CRm ++ x.op2 ++ x._fixed2

/-- (FV addition) Barriers: `DMB` (the backend emits only `dmb ish`; the `11` at bits 13:12
selects DMB over DSB/ISB, so the class is fixed to DMB). -/
structure Barrier_cls where
  _fixed1 : BitVec 20 := 0b11010101000000110011#20 -- [31:12]
  CRm     : BitVec 4                               -- [11:8]
  op2     : BitVec 3                               -- [7:5]
  _fixed2 : BitVec 5 := 0b11111#5                  -- [4:0]
deriving DecidableEq, Repr

instance : ToString Barrier_cls where toString a := toString (repr a)

def Barrier_cls.toBitVec32 (x : Barrier_cls) : BitVec 32 :=
  x._fixed1 ++ x.CRm ++ x.op2 ++ x._fixed2

/-- (FV addition) Move from system register: `MRS Xt, (op0 = 2 + o0, op1, CRn, CRm, op2)`
(the backend emits only `mrs xt, tpidr_el0`: o0 1, op1 011, CRn 1101, CRm 0000, op2 010). -/
structure Mrs_cls where
  _fixed1 : BitVec 12 := 0b110101010011#12 -- [31:20]
  o0      : BitVec 1                       -- [19:19]
  op1     : BitVec 3                       -- [18:16]
  CRn     : BitVec 4                       -- [15:12]
  CRm     : BitVec 4                       -- [11:8]
  op2     : BitVec 3                       -- [7:5]
  Rt      : BitVec 5                       -- [4:0]
deriving DecidableEq, Repr

instance : ToString Mrs_cls where toString a := toString (repr a)

def Mrs_cls.toBitVec32 (x : Mrs_cls) : BitVec 32 :=
  x._fixed1 ++ x.o0 ++ x.op1 ++ x.CRn ++ x.CRm ++ x.op2 ++ x.Rt

/-- (FV addition) Test and branch (immediate): `TBZ`, `TBNZ`. -/
structure Test_branch_cls where
  b5     : BitVec 1               -- [31:31]
  _fixed : BitVec 6 := 0b011011#6 -- [30:25]
  op     : BitVec 1               -- [24:24]
  b40    : BitVec 5               -- [23:19]
  imm14  : BitVec 14              -- [18:5]
  Rt     : BitVec 5               --  [4:0]
deriving DecidableEq, Repr

instance : ToString Test_branch_cls where toString a := toString (repr a)

def Test_branch_cls.toBitVec32 (x : Test_branch_cls) : BitVec 32 :=
  x.b5 ++ x._fixed ++ x.op ++ x.b40 ++ x.imm14 ++ x.Rt

inductive BranchInst where
  | Compare_branch :
    Compare_branch_cls → BranchInst
  | Uncond_branch_imm :
    Uncond_branch_imm_cls → BranchInst
  | Uncond_branch_reg :
    Uncond_branch_reg_cls → BranchInst
  | Cond_branch_imm :
    Cond_branch_imm_cls → BranchInst
  | Hints :
    Hints_cls → BranchInst
  | Barrier :
    Barrier_cls → BranchInst
  | Test_branch :
    Test_branch_cls → BranchInst
  | Mrs :
    Mrs_cls → BranchInst
deriving DecidableEq, Repr

instance : ToString BranchInst where toString a := toString (repr a)

end Decode

end Arm
