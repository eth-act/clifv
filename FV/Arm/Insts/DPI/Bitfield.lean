/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Nevine
-/

--   UBFM (immediate) 32- and 64-bit versions
--        (aliased as LSL (immediate), LSR (immediate), UBFIZ, UBFX, UXTB, and UXTH)
--   SBFM (immediate) 32- and 64-bit versions
--        (aliased as ASR (immediate), SBFIZ, SBFX, SXTB, SXTH, and SXTW)
--   BFM (immediate) 32- and 64-bit versions
--        (aliased as BFC, BFI, and BFXIL)

import FV.Arm.Decode
import FV.Arm.Insts.Common

namespace Arm


namespace DPI

open _root_.BitVec Arm.BitVec

@[state_simp_rules]
def exec_bitfield (inst: Bitfield_cls) (s : ArmState) : ArmState :=
  let (err, inzero, extend) :=
    match inst.opc with
    | 0b00#2 => (false, true, true)   -- SBFM
    | 0b01#2 => (false, false, false) -- BFM
    | 0b10#2 => (false, true, false)  -- UBFM
    | 0b11#2 => (true,  false, false) -- Undefined
  if err then
    write_err (StateError.Unimplemented s!"Illegal {inst} encountered!") s
  else
    let immr5 := lsb inst.immr 5
    let imms5 := lsb inst.imms 5
    if (inst.sf = 1#1 ∧ inst.N ≠ 1#1) ∨
      (inst.sf = 0#1 ∧ (inst.N ≠ 0#1 ∨ immr5 ≠ 0#1 ∨ imms5 ≠ 0#1)) then
      write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
    else
      let datasize  := if inst.sf = 1#1 then 64 else 32
      let wtmask    := decode_bit_masks inst.N inst.imms inst.immr false datasize
      match wtmask with
      | none => write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
      | some (wmask, tmask) =>
        let dst := if inzero then (BitVec.zero datasize) else (read_gpr_zr datasize inst.Rd s)
        let src := read_gpr_zr datasize inst.Rn s
        -- Perform bitfield move on low bits
        let bot := (dst &&& ~~~wmask) ||| ((BitVec.ror src inst.immr.toNat) &&& wmask)
        -- Determine extension bits (sign, zero or dest register)
        have h : 1 * datasize = datasize := by simp only [Nat.one_mul]
        let src_s := BitVec.lsb src inst.imms.toNat
        let top : BitVec datasize :=
          if extend then
            BitVec.cast h $ BitVec.replicate datasize src_s
          else
            dst
        -- Combine extension bits and result bits
        let result := (top &&& ~~~tmask) ||| (bot &&& tmask)
        let s := write_gpr_zr datasize inst.Rd result s
        let s := write_pc ((read_pc s) + 4#64) s
        s

----------------------------------------------------------------------

-- We have separate functions to test LSR and LSL specifically
-- because we want to make sure they are hit during conformance testing,
-- which may not be the case when `Bitfield_cls.all.rand` is used to
-- generate a small number of test cases.
----------------------------------------------------------------------

end DPI

end Arm
