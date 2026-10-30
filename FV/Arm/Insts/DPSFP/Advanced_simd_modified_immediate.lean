/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- MOVI, MVNI, ORR, BIC (Immediate, vector), and FMOV (vector, immediate) - Single/double-precision
-- Missing: FMOV (vector, immediate) - Half-precision
-- Modified by fv-compiler-rust (2026): ported to Lean v4.34.1 (module prefix FV.Arm, namespace
-- Arm); the `reduceAdvSIMDExpandImm` dsimproc and the LNSym `CosimM` generators are dropped
-- (co-simulation: FVTest/Arm/Cosim); `decode_immediate_op` returns only the operation (the
-- error write for the unallocated encodings moved to `exec_advanced_simd_modified_immediate`). Arm ARM (DDI 0487) "MOVI", "MVNI", "ORR (vector,
-- immediate)", "BIC (vector, immediate)", "FMOV (vector, immediate)"; `AdvSIMDExpandImm`
-- (shared/functions/vector/advsimdexpandimm). Cranelift emits `movi vd.2s, #0` for a zero
-- `f32const`/`f64const` (`constant_f32`/`constant_f64`, `MInst.VecDupImm`).

import FV.Arm.Decode.DPSFP
import FV.Arm.Insts.Common
import FV.Arm.BitVec

namespace Arm

----------------------------------------------------------------------

namespace DPSFP

open _root_.BitVec Arm.BitVec

inductive ImmediateOp where
  | MOVI : ImmediateOp
  | MVNI : ImmediateOp
  | ORR : ImmediateOp
  | BIC : ImmediateOp
deriving DecidableEq, Repr

instance : ToString ImmediateOp where toString a := toString (repr a)

/-- The operation of an encoding; `none` for the unallocated ones. -/
@[state_simp_rules]
def decode_immediate_op (inst : Advanced_simd_modified_immediate_cls) : Option ImmediateOp :=
  -- All UNALLOCATED cases when inst.o2 = 1
  if inst.o2 = 0b1#1 ∧ inst.cmode ++ inst.op ≠ 0b11110#5 then
    none
  else
    match_bv inst.cmode ++ inst.op with
    | [0, _xx:2, 00] => some ImmediateOp.MOVI
    | [0, _xx:2, 01] => some ImmediateOp.MVNI
    | [0, _xx:2, 10] => some ImmediateOp.ORR
    | [0, _xx:2, 11] => some ImmediateOp.BIC
    | [10, _x:1, 00] => some ImmediateOp.MOVI
    | [10, _x:1, 01] => some ImmediateOp.MVNI
    | [10, _x:1, 10] => some ImmediateOp.ORR
    | [10, _x:1, 11] => some ImmediateOp.BIC
    | [110, _x:1, 0] => some ImmediateOp.MOVI
    | [110, _x:1, 1] => some ImmediateOp.MVNI
    | [1110, _x:1] => some ImmediateOp.MOVI
    | [11110] => some ImmediateOp.MOVI
    -- | case [11111]
    | _ => if inst.Q = 0#1 then none else some ImmediateOp.MOVI

def AdvSIMDExpandImm (op : BitVec 1) (cmode : BitVec 4) (imm8 : BitVec 8) : BitVec 64 :=
  let cmode_high3 := extractLsb' 1 3 cmode
  let cmode_low1 := lsb cmode 0
  match cmode_high3 with
  | 0b000#3 => replicate 2 $ BitVec.zero 24 ++ imm8
  | 0b001#3 => replicate 2 $ BitVec.zero 16 ++ imm8 ++ BitVec.zero 8
  | 0b010#3 => replicate 2 $ BitVec.zero 8 ++ imm8 ++ BitVec.zero 16
  | 0b011#3 => replicate 2 $ imm8 ++ BitVec.zero 24
  | 0b100#3 => replicate 4 $ BitVec.zero 8 ++ imm8
  | 0b101#3 => replicate 4 $ imm8 ++ BitVec.zero 8
  | 0b110#3 =>
    if cmode_low1 = 0 then
      replicate 2 $ BitVec.zero 16 ++ imm8 ++ allOnes 8
    else
      replicate 2 $ BitVec.zero 8 ++ imm8 ++ allOnes 16
  | _ =>
    if cmode_low1 = 0 ∧ op = 0 then
      replicate 8 imm8
    else if cmode_low1 = 0 ∧ op = 1 then
      let imm8a := replicate 8 $ lsb imm8 7
      let imm8b := replicate 8 $ lsb imm8 6
      let imm8c := replicate 8 $ lsb imm8 5
      let imm8d := replicate 8 $ lsb imm8 4
      let imm8e := replicate 8 $ lsb imm8 3
      let imm8f := replicate 8 $ lsb imm8 2
      let imm8g := replicate 8 $ lsb imm8 1
      let imm8h := replicate 8 $ lsb imm8 0
      imm8a ++ imm8b ++ imm8c ++ imm8d ++ imm8e ++ imm8f ++ imm8g ++ imm8h
    else if cmode_low1 = 1 ∧ op = 0 then
      let imm32 := lsb imm8 7 ++ ~~~(lsb imm8 6) ++
                   (replicate 5 $ lsb imm8 6) ++
                   extractLsb' 0 6 imm8 ++ BitVec.zero 19
      replicate 2 imm32
    else
      -- Assume not UsingAArch32()
      -- if UsingAArch32() then ReservedEncoding();
      lsb imm8 7 ++ ~~~(lsb imm8 6) ++
        (replicate 8 $ lsb imm8 6) ++ extractLsb' 0 6 imm8 ++ BitVec.zero 48

@[state_simp_rules]
-- Assumes CheckFPAdvSIMDEnabled64();
def exec_advanced_simd_modified_immediate
  (inst : Advanced_simd_modified_immediate_cls) (s : ArmState) : ArmState :=
  match decode_immediate_op inst with
  | none => write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  | some operation =>
    let datasize := 64 <<< inst.Q.toNat
    let imm8 := inst.a ++ inst.b ++ inst.c ++ inst.d ++ inst.e ++ inst.f ++ inst.g ++ inst.h
    let imm16 : BitVec 16 :=
                 extractLsb' 7 1 imm8 ++ ~~~ (extractLsb' 6 1 imm8) ++
                 (replicate 2 $ extractLsb' 6 1 imm8) ++
                 extractLsb' 0 6 imm8 ++ BitVec.zero 6
    let imm64 := AdvSIMDExpandImm inst.op inst.cmode imm8
    have h₁ : 16 * (datasize / 16) = datasize := by omega
    have h₂ : 64 * (datasize / 64) = datasize := by omega
    -- Assumes IsFeatureImplemented(FEAT_FP16)
    let imm : BitVec datasize :=
      if inst.op ++ inst.cmode ++ inst.o2 = 0b011111#6
      then BitVec.cast h₁ $ replicate (datasize/16) imm16
      else BitVec.cast h₂ $ replicate (datasize/64) imm64
    let result := match operation with
                | ImmediateOp.MOVI => imm
                | ImmediateOp.MVNI => ~~~imm
                | ImmediateOp.ORR =>
                  let operand := read_sfp datasize inst.Rd s
                  operand ||| imm
                | _ =>
                  let operand := read_sfp datasize inst.Rd s
                  operand &&& ~~~imm
    -- State Updates
    let s := write_pc ((read_pc s) + 4#64) s
    let s := write_sfp datasize inst.Rd result s
    s

end DPSFP

end Arm
