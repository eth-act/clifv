/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- FMOV (general)
-- Modified by fv-compiler-rust (2026): the general-register operand is `X[n]`/`X[d]` in the
-- Arm ARM ASL (`intval = X[n, intsize]`, `X[d, intsize] = intval`), so register 31 is XZR, not
-- SP (upstream used the SP-flavoured accessors; found by co-simulation).

import FV.Arm.Decode
import FV.Arm.Insts.Common
import FV.Arm.BitVec

namespace Arm


----------------------------------------------------------------------

namespace DPSFP

open _root_.BitVec Arm.BitVec

@[state_simp_rules]
def fmov_general_aux (intsize : Nat) (fltsize : Nat) (op : FPConvOp)
  (part : Nat) (inst : Conversion_between_FP_and_Int_cls) (s : ArmState)
  : ArmState :=
  -- Assume CheckFPEnabled64()
  match op with
  | FPConvOp.FPConvOp_MOV_FtoI =>
    let fltval := Vpart_read inst.Rn part fltsize s
    let intval := zeroExtend intsize fltval
    -- State Update
    let s := write_gpr_zr intsize inst.Rd intval s
    let s := write_pc ((read_pc s) + 4#64) s
    s
  | FPConvOp.FPConvOp_MOV_ItoF =>
    let intval := read_gpr_zr intsize inst.Rn s
    let fltval := extractLsb' 0 fltsize intval
    -- State Update
    let s := Vpart_write inst.Rd part fltsize fltval s
    let s := write_pc ((read_pc s) + 4#64) s
    s
  | _ => write_err (StateError.Other s!"fmov_general_aux called with non-FMOV op!") s

@[state_simp_rules]
def exec_fmov_general
  (inst : Conversion_between_FP_and_Int_cls) (s : ArmState): ArmState :=
  let intsize := 32 <<< inst.sf.toNat
  let decode_fltsize := if inst.ftype = 0b10#2 then 64 else (8 <<< (inst.ftype ^^^ 0b10#2).toNat)
  match (extractLsb' 1 2 inst.opcode) ++ inst.rmode with
  | 0b1100 =>  -- FMOV
    if decode_fltsize ≠ 16 ∧ decode_fltsize ≠ intsize then
      write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
    else
      let op := if lsb inst.opcode 0 = 1#1
                then FPConvOp.FPConvOp_MOV_ItoF
                else FPConvOp.FPConvOp_MOV_FtoI
      let part := 0
      fmov_general_aux intsize decode_fltsize op part inst s
  | 0b1101 => -- FMOV D[1]
    if intsize ≠ 64 ∨ inst.ftype ≠ 0b10#2 then
      write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
    else
      let op := if lsb inst.opcode 0 = 1#1
                then FPConvOp.FPConvOp_MOV_ItoF
                else FPConvOp.FPConvOp_MOV_FtoI
      let part := 1
      fmov_general_aux intsize decode_fltsize op part inst s
    | _ => write_err (StateError.Other s!"exec_fmov_general called with non-FMOV instructions!") s

@[state_simp_rules]
def exec_conversion_between_FP_and_Int
  (inst : Conversion_between_FP_and_Int_cls) (s : ArmState) : ArmState :=
  if inst.ftype = 0b10#2 ∧ (extractLsb' 1 2 inst.opcode) ++ inst.rmode ≠ 0b1101#4 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
    -- Assume IsFeatureImplemented(FEAT_FP16) is true
  else
    match_bv inst.sf ++ inst.S ++ inst.ftype ++ inst.rmode ++ inst.opcode with
    | [_sf:1, 0, _ftype:2, 0, _rmode0:1, 11, _opcode0:1] => exec_fmov_general inst s
    | _ => write_err (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!") s

----------------------------------------------------------------------

end DPSFP

end Arm
