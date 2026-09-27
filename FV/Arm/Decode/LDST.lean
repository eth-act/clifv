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

-- Load and Store Instructions

structure Reg_imm_post_indexed_cls where
  size    : BitVec 2            -- [31:30]
  _fixed1 : BitVec 3 := 0b111#3 -- [29:27]
  V       : BitVec 1            -- [26:26]
  _fixed2 : BitVec 2 := 0b00#2  -- [25:24]
  opc     : BitVec 2            -- [23:22]
  _fixed3 : BitVec 1 := 0b0#1   -- [21:21]
  imm9    : BitVec 9            -- [20:12]
  _fixed4 : BitVec 2 := 0b01#2  -- [11:10]
  Rn      : BitVec 5            --   [9:5]
  Rt      : BitVec 5            --   [4:0]
deriving DecidableEq, Repr

instance : ToString Reg_imm_post_indexed_cls where toString a := toString (repr a)

structure Reg_unsigned_imm_cls where
  size    : BitVec 2            -- [31:30]
  _fixed1 : BitVec 3 := 0b111#3 -- [29:27]
  V       : BitVec 1            -- [26:26]
  _fixed2 : BitVec 2 := 0b01#2  -- [25:24]
  opc     : BitVec 2            -- [23:22]
  imm12   : BitVec 12           -- [21:10]
  Rn      : BitVec 5            --   [9:5]
  Rt      : BitVec 5            --   [4:0]
deriving DecidableEq, Repr

instance : ToString Reg_unsigned_imm_cls where toString a := toString (repr a)

structure Reg_unscaled_imm_cls where
  size    : BitVec 2            -- [31:30]
  _fixed1 : BitVec 3 := 0b111#3 -- [29:27]
  VR      : BitVec 1            -- [26:26]
  _fixed2 : BitVec 2 := 0b00#2  -- [25:24]
  opc     : BitVec 2            -- [23:22]
  _fixed3 : BitVec 1 := 0b0#1   -- [21:21]
  imm9    : BitVec 9            -- [20:12]
  _fixed4 : BitVec 2 := 0b00#2  -- [11:10]
  Rn      : BitVec 5            --   [9:5]
  Rt      : BitVec 5            --   [4:0]
deriving DecidableEq, Repr

instance : ToString Reg_unscaled_imm_cls where toString a := toString (repr a)

structure Reg_pair_pre_indexed_cls where
  opc     : BitVec 2            -- [31:30]
  _fixed1 : BitVec 3 := 0b101#3 -- [29:27]
  V       : BitVec 1            -- [26:26]
  _fixed2 : BitVec 3 := 0b011#3 -- [25:23]
  L       : BitVec 1            -- [22:22]
  imm7    : BitVec 7            -- [21:15]
  Rt2     : BitVec 5            -- [14:10]
  Rn      : BitVec 5            --   [9:5]
  Rt      : BitVec 5            --   [4:0]
deriving DecidableEq, Repr

instance : ToString Reg_pair_pre_indexed_cls where toString a := toString (repr a)

structure Reg_pair_post_indexed_cls where
  opc     : BitVec 2            -- [31:30]
  _fixed1 : BitVec 3 := 0b101#3 -- [29:27]
  V       : BitVec 1            -- [26:26]
  _fixed2 : BitVec 3 := 0b001#3 -- [25:23]
  L       : BitVec 1            -- [22:22]
  imm7    : BitVec 7            -- [21:15]
  Rt2     : BitVec 5            -- [14:10]
  Rn      : BitVec 5            --   [9:5]
  Rt      : BitVec 5            --   [4:0]
deriving DecidableEq, Repr

instance : ToString Reg_pair_post_indexed_cls where toString a := toString (repr a)

structure Reg_pair_signed_offset_cls where
  opc     : BitVec 2            -- [31:30]
  _fixed1 : BitVec 3 := 0b101#3 -- [29:27]
  V       : BitVec 1            -- [26:26]
  _fixed2 : BitVec 3 := 0b010#3 -- [25:23]
  L       : BitVec 1            -- [22:22]
  imm7    : BitVec 7            -- [21:15]
  Rt2     : BitVec 5            -- [14:10]
  Rn      : BitVec 5            --   [9:5]
  Rt      : BitVec 5            --   [4:0]
deriving DecidableEq, Repr

instance : ToString Reg_pair_signed_offset_cls where toString a := toString (repr a)

/-- (FV addition) Load/store register (immediate pre-indexed). -/
structure Reg_imm_pre_indexed_cls where
  size    : BitVec 2            -- [31:30]
  _fixed1 : BitVec 3 := 0b111#3 -- [29:27]
  V       : BitVec 1            -- [26:26]
  _fixed2 : BitVec 2 := 0b00#2  -- [25:24]
  opc     : BitVec 2            -- [23:22]
  _fixed3 : BitVec 1 := 0b0#1   -- [21:21]
  imm9    : BitVec 9            -- [20:12]
  _fixed4 : BitVec 2 := 0b11#2  -- [11:10]
  Rn      : BitVec 5            --   [9:5]
  Rt      : BitVec 5            --   [4:0]
deriving DecidableEq, Repr

instance : ToString Reg_imm_pre_indexed_cls where toString a := toString (repr a)

/-- (FV addition) Load/store register (register offset). -/
structure Reg_reg_offset_cls where
  size    : BitVec 2            -- [31:30]
  _fixed1 : BitVec 3 := 0b111#3 -- [29:27]
  V       : BitVec 1            -- [26:26]
  _fixed2 : BitVec 2 := 0b00#2  -- [25:24]
  opc     : BitVec 2            -- [23:22]
  _fixed3 : BitVec 1 := 0b1#1   -- [21:21]
  Rm      : BitVec 5            -- [20:16]
  option  : BitVec 3            -- [15:13]
  S       : BitVec 1            -- [12:12]
  _fixed4 : BitVec 2 := 0b10#2  -- [11:10]
  Rn      : BitVec 5            --   [9:5]
  Rt      : BitVec 5            --   [4:0]
deriving DecidableEq, Repr

instance : ToString Reg_reg_offset_cls where toString a := toString (repr a)

inductive LDSTInst where
  | Reg_imm_post_indexed :
    Reg_imm_post_indexed_cls → LDSTInst
  | Reg_unsigned_imm :
    Reg_unsigned_imm_cls → LDSTInst
  | Reg_unscaled_imm :
    Reg_unscaled_imm_cls  → LDSTInst
  | Reg_pair_pre_indexed :
    Reg_pair_pre_indexed_cls → LDSTInst
  | Reg_pair_post_indexed :
    Reg_pair_post_indexed_cls → LDSTInst
  | Reg_pair_signed_offset :
    Reg_pair_signed_offset_cls → LDSTInst
  | Reg_imm_pre_indexed :
    Reg_imm_pre_indexed_cls → LDSTInst
  | Reg_reg_offset :
    Reg_reg_offset_cls → LDSTInst
deriving DecidableEq, Repr

instance : ToString LDSTInst where toString a := toString (repr a)

end Decode

end Arm
