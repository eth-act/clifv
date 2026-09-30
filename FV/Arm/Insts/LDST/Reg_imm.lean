/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Yan Peng
-/
-- LDR/STR (immediate, post-indexed and unsigned offset, GPR and SIMD&FP)
-- LDRB/STRB (immediate, post-indexed and unsigned offset, GPR)
-- Modified by fv-compiler-rust (2026): ported to Lean v4.34.1, module prefix FV.Arm, wrapped in
-- namespace Arm. The GPR path now follows the shared Arm ARM (DDI 0487) ASL decode of
-- "Load/store register (unsigned immediate / unscaled immediate / immediate pre-indexed /
-- immediate post-indexed / register offset)" for every size and opc (upstream: STR/LDR/STRB/LDRB
-- only), i.e. also LDRH/STRH, LDRSB, LDRSH, LDRSW, and register `Rt = 31` is `XZR`/`WZR`
-- (upstream read SP). Offsets are a `Reg_offset` (upstream: `BitVec 12 ⊕ BitVec 9`) so the
-- register-offset form shares the operation. ASL (GPR decode, per `size`/`opc`):
--
--   if opc<1> == '0' then   // store or zero-extending load
--       memop = if opc<0> == '1' then MemOp_LOAD else MemOp_STORE;
--       regsize = if size == '11' then 64 else 32; signed = FALSE;
--   else
--       if size == '11' then memop = MemOp_PREFETCH; if opc<0> == '1' then UNDEFINED;
--       else                 // sign-extending load
--           memop = MemOp_LOAD;
--           if size == '10' && opc<0> == '1' then UNDEFINED;
--           regsize = if opc<0> == '1' then 32 else 64; signed = TRUE;
--   integer datasize = 8 << scale;
--
-- Operation (all addressing modes):
--
--   if n == 31 then CheckSPAlignment(); address = SP[]; else address = X[n];
--   if !postindex then address = address + offset;
--   case memop of
--     when MemOp_STORE data = X[t, datasize]; Mem[address, datasize DIV 8] = data;
--     when MemOp_LOAD  data = Mem[address, datasize DIV 8];
--                      X[t, regsize] = if signed then SignExtend(data, regsize)
--                                                else ZeroExtend(data, regsize);
--   if wback then
--     if postindex then address = address + offset;
--     if n == 31 then SP[] = address; else X[n] = address;
--
-- Cross-checked against VeriISLE `MInst.ULoad8/16/32/64`, `SLoad8/16/32`, `Store8/16/32/64`
-- (cranelift/codegen/src/isa/aarch64/spec/{loads,stores}.isle).

import FV.Arm.Decode
import FV.Arm.Insts.Common

namespace Arm


----------------------------------------------------------------------

namespace LDST

open _root_.BitVec Arm.BitVec

/-- (FV) The offset operand of a single-register load/store. -/
inductive Reg_offset where
  /-- Unsigned 12-bit immediate, scaled by the access size ("unsigned offset"). -/
  | uimm12 : BitVec 12 → Reg_offset
  /-- Signed 9-bit immediate, unscaled (unscaled, pre- and post-indexed forms). -/
  | simm9  : BitVec 9 → Reg_offset
  /-- Register offset `Rm`, extended by `option` and shifted by `scale` iff `S = 1`. -/
  | reg    : (Rm : BitVec 5) → (option : BitVec 3) → (S : BitVec 1) → Reg_offset
deriving DecidableEq, Repr

structure Reg_imm_cls where
  size      : BitVec 2
  opc       : BitVec 2
  Rn        : BitVec 5
  Rt        : BitVec 5
  SIMD?     : Bool
  wback     : Bool
  postindex : Bool
  imm       : Reg_offset
deriving DecidableEq, Repr

instance : ToString Reg_imm_cls where toString a := toString (repr a)

/-- The byte offset added to the base register (ASL `offset`). -/
@[state_simp_rules]
def Reg_offset.value (o : Reg_offset) (scale : Nat) (s : ArmState) : BitVec 64 :=
  match o with
  | .uimm12 imm12 => (BitVec.zeroExtend 64 imm12) <<< scale
  | .simm9 imm9 => signExtend 64 imm9
  | .reg Rm option S =>
    -- ASL: `integer shift = if S == '1' then scale else 0;`
    --      `bits(64) offset = ExtendReg(m, extend_type, shift, 64);`
    extend_reg (read_gpr_zr 64 Rm s) (decode_reg_extend option) (if S = 1#1 then scale else 0)

@[state_simp_rules]
def reg_imm_operation (inst_str : String) (op : BitVec 1) (signed : Bool)
  (wback : Bool) (postindex : Bool) (SIMD? : Bool)
  (datasize : Nat) (regsize : Nat) (Rn : BitVec 5)
  (Rt : BitVec 5) (offset : BitVec 64) (s : ArmState)
  (H : 8 ∣ datasize) : ArmState :=
  let address := read_gpr 64 Rn s
  if Rn = 31#5 ∧ ¬(CheckSPAlignment s) then
      write_err (StateError.Fault s!"[Inst: {inst_str}] SP {address} is not aligned!") s
      -- Note: we do not need to model the ASL function
      -- "CreateAccDescGPR" here, given the simplicity of our memory
      -- model
  else
    let address := if postindex then address else address + offset
    have h : datasize / 8 * 8 = datasize := by
      exact Nat.div_mul_cancel H
    let s :=
      match op with
      | 0#1 => -- STORE
        let data := ldst_read SIMD? datasize Rt s
        write_mem_bytes (datasize / 8) address (BitVec.cast h.symm data) s
      | _ => -- LOAD
        let data := BitVec.cast h (read_mem_bytes (datasize / 8) address s)
        if SIMD? then write_sfp datasize Rt data s
        else write_gpr_zr regsize Rt
               (if signed then signExtend regsize data else zeroExtend regsize data) s
    if wback then
      let address := if postindex then address + offset else address
      write_gpr 64 Rn address s
    else
      s

@[state_simp_rules]
def reg_imm_constrain_unpredictable (wback : Bool) (SIMD? : Bool) (Rn : BitVec 5)
  (Rt : BitVec 5) : Bool :=
  if SIMD? then false else wback ∧ Rn = Rt ∧ Rn ≠ 31#5

/-- SIMD&FP forms supported by upstream LNSym (unchanged). -/
@[state_simp_rules]
def supported_simd_reg_imm (size : BitVec 2) (opc : BitVec 2) : Bool :=
  match size, opc with
  | _, 0b00#2 => true      -- STR, 8-bit, 16-bit, 32-bit, 64-bit, SIMD&FP
  | _, 0b01#2 => true      -- LDR, 8-bit, 16-bit, 32-bit, 64-bit, SIMD&FP
  | 0b00#2, 0b10#2 => true -- STR, 128-bit, SIMD&FP
  | 0b00#2, 0b11#2 => true -- LDR, 128-bit, SIMD&FP
  | _, _ => false -- other instructions that are not supported or illegal

@[state_simp_rules]
def exec_reg_imm_common
  (inst : Reg_imm_cls) (inst_str : String) (s : ArmState) : ArmState :=
  let scale :=
    if inst.SIMD? then ((lsb inst.opc 1) ++ inst.size).toNat
    else inst.size.toNat
  if inst.SIMD? ∧ ¬ supported_simd_reg_imm inst.size inst.opc then
    write_err (StateError.Unimplemented s!"Unsupported instruction {inst_str} encountered!") s
  -- UNDEFINED case in LDR/STR SIMD/FP instructions
  -- FIXME: prove that this branch condition is trivially false
  else if inst.SIMD? ∧ scale > 4 then
    write_err (StateError.Illegal s!"Illegal instruction {inst_str} encountered!") s
  -- GPR, size = 11, opc = 10: PRFM / PRFUM (prefetch); not modelled.
  else if ¬ inst.SIMD? ∧ inst.size = 0b11#2 ∧ inst.opc = 0b10#2 then
    write_err (StateError.Unimplemented s!"Unsupported instruction {inst_str} encountered!") s
  -- GPR, opc = 11 with size = 1x: UNDEFINED.
  else if ¬ inst.SIMD? ∧ lsb inst.size 1 = 1#1 ∧ inst.opc = 0b11#2 then
    write_err (StateError.Illegal s!"Illegal instruction {inst_str} encountered!") s
  -- constrain unpredictable when GPR
  else if reg_imm_constrain_unpredictable inst.wback inst.SIMD? inst.Rn inst.Rt then
    write_err (StateError.Illegal s!"Illegal instruction {inst_str} encountered!") s
  else
    let offset := inst.imm.value scale s
    let datasize := 8 <<< scale
    -- GPR decode (see the header): `opc<1> = 1` is a sign-extending load.
    let signed := ¬ inst.SIMD? ∧ lsb inst.opc 1 = 1#1
    let memop : BitVec 1 := if signed then 1#1 else lsb inst.opc 0
    let regsize :=
      if lsb inst.opc 1 = 0#1 then (if inst.size = 0b11#2 then 64 else 32)
      else (if lsb inst.opc 0 = 1#1 then 32 else 64)
    have H : 8 ∣ datasize := by
      simp_all! only [Nat.shiftLeft_eq, Nat.dvd_mul_right, datasize]
    -- State Updates
    let s' := reg_imm_operation inst_str
              memop signed inst.wback inst.postindex
              inst.SIMD? datasize regsize inst.Rn inst.Rt offset s (H)
    let s' := write_pc ((read_pc s) + 4#64) s'
    s'

@[state_simp_rules]
def exec_reg_imm_unsigned_offset
  (inst : Reg_unsigned_imm_cls) (s : ArmState) : ArmState :=
  let extracted_inst : Reg_imm_cls :=
    { size      := inst.size,
      opc       := inst.opc,
      Rn        := inst.Rn,
      Rt        := inst.Rt,
      SIMD?     := inst.V = 1#1,
      wback     := false,
      postindex := false,
      imm       := .uimm12 inst.imm12 }
  exec_reg_imm_common extracted_inst s!"{inst}" s

@[state_simp_rules]
def exec_reg_imm_post_indexed
  (inst : Reg_imm_post_indexed_cls) (s : ArmState) : ArmState :=
  let extracted_inst : Reg_imm_cls :=
    { size      := inst.size,
      opc       := inst.opc,
      Rn        := inst.Rn,
      Rt        := inst.Rt,
      SIMD?     := inst.V = 1#1,
      wback     := true,
      postindex := true,
      imm       := .simm9 inst.imm9 }
  exec_reg_imm_common extracted_inst s!"{inst}" s

/-- (FV addition) Load/store register (immediate pre-indexed), e.g. `str x21, [sp, #-16]!`. -/
@[state_simp_rules]
def exec_reg_imm_pre_indexed
  (inst : Reg_imm_pre_indexed_cls) (s : ArmState) : ArmState :=
  let extracted_inst : Reg_imm_cls :=
    { size      := inst.size,
      opc       := inst.opc,
      Rn        := inst.Rn,
      Rt        := inst.Rt,
      SIMD?     := inst.V = 1#1,
      wback     := true,
      postindex := false,
      imm       := .simm9 inst.imm9 }
  exec_reg_imm_common extracted_inst s!"{inst}" s

/-- (FV addition) Load/store register (unscaled immediate), GPR: `LDUR*`/`STUR*`.
(The SIMD&FP forms stay in `exec_ldstur`, as upstream.) -/
@[state_simp_rules]
def exec_reg_unscaled_imm_gpr
  (inst : Reg_unscaled_imm_cls) (s : ArmState) : ArmState :=
  let extracted_inst : Reg_imm_cls :=
    { size      := inst.size,
      opc       := inst.opc,
      Rn        := inst.Rn,
      Rt        := inst.Rt,
      SIMD?     := false,
      wback     := false,
      postindex := false,
      imm       := .simm9 inst.imm9 }
  exec_reg_imm_common extracted_inst s!"{inst}" s

/-- (FV addition) Load/store register (register offset), GPR:
`LDR/STR/LDRB/STRB/LDRH/STRH/LDRSB/LDRSH/LDRSW Rt, [Xn, Rm{, extend {#amount}}]`.
ASL decode addition: `if option<1> == '0' then UNDEFINED;`. SIMD&FP register-offset forms are
not modelled (Cranelift does not emit them for the emitter subset). -/
@[state_simp_rules]
def exec_reg_reg_offset
  (inst : Reg_reg_offset_cls) (s : ArmState) : ArmState :=
  if inst.V = 1#1 then
    write_err (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!") s
  else if lsb inst.option 1 = 0#1 then
    write_err (StateError.Illegal s!"Illegal instruction {inst} encountered!") s
  else
    let extracted_inst : Reg_imm_cls :=
      { size      := inst.size,
        opc       := inst.opc,
        Rn        := inst.Rn,
        Rt        := inst.Rt,
        SIMD?     := false,
        wback     := false,
        postindex := false,
        imm       := .reg inst.Rm inst.option inst.S }
    exec_reg_imm_common extracted_inst s!"{inst}" s

/-- (FV addition) Load/store exclusive / acquire-release, GPR only:
`LDXR/LDAXR/STXR/STLXR/LDAR/STLR Rt, [Xn]`.
Single-threaded ASL: an exclusive load is the plain load (zero-extended, `regsize` 64 at
`size = 11`, else 32); an exclusive store writes memory and the *success flag* `0` to `Rs`
(`STXR`/`STLXR` always succeed). No exclusive-monitor state: `Clif.run`'s single-thread
semantics of the CLIF atomics match (`FV/Clif/Run.lean`), and Cranelift's LL/SC loops
retry on failure only, which cannot happen here. -/
@[state_simp_rules]
def exec_reg_exclusive (inst : Reg_exclusive_cls) (s : ArmState) : ArmState :=
  let scale := inst.size.toNat
  let datasize := 8 <<< scale
  if inst.Rn = 31#5 ∧ ¬(CheckSPAlignment s) then
    write_err (StateError.Fault s!"[Inst: {inst}] SP is not aligned!") s
  else
    let address := read_gpr 64 inst.Rn s
    have H : datasize / 8 * 8 = datasize := by
      have h8 : 8 ∣ datasize := by simp only [datasize, Nat.shiftLeft_eq]; omega
      exact Nat.div_mul_cancel h8
    let s :=
      if inst.L = 1#1 then
        let regsize := if inst.size = 0b11#2 then 64 else 32
        let data := BitVec.cast H (read_mem_bytes (datasize / 8) address s)
        write_gpr_zr regsize inst.Rt (zeroExtend regsize data) s
      else
        let data := ldst_read false datasize inst.Rt s
        let s := write_mem_bytes (datasize / 8) address (BitVec.cast H.symm data) s
        -- the exclusive store succeeds: `Rs` gets 0 (the W-register write zero-extends)
        write_gpr_zr 32 inst.Rs (0x0 : BitVec 32) s
    write_pc ((read_pc s) + 4#64) s

end LDST

end Arm
