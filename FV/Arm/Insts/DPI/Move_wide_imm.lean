/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- MOVZ, MOVK and MOVN
-- Modified by fv-compiler-rust (2026): ported to Lean v4.34.1, module prefix FV.Arm, wrapped in
-- namespace Arm; `Rd = 31` is XZR per the Arm ARM (DDI 0487) ASL `X[d, datasize]` (upstream
-- read and wrote SP).

import FV.Arm.Decode
import FV.Arm.Insts.Common

namespace Arm


namespace DPI

open _root_.BitVec Arm.BitVec

@[state_simp_rules]
def exec_move_wide_imm (inst : Move_wide_imm_cls) (s : ArmState) : ArmState :=
  if inst.opc = 0b01#2 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else if inst.sf = 0#1 ∧ getLsbD inst.hw 1 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize := 32 <<< inst.sf.toNat
    let pos := (inst.hw ++ 0b0000#4).toNat
    let result := if inst.opc = 0b11#2
                  then read_gpr_zr datasize inst.Rd s
                  else BitVec.zero datasize
    let result := partInstall pos 16 inst.imm16 result
    let result := if inst.opc = 0b00#2 then ~~~result else result
    -- State Update
    let s := write_gpr_zr datasize inst.Rd result s
    let s := write_pc ((read_pc s) + 4#64) s
    s

----------------------------------------------------------------------

----------------------------------------------------------------------

end DPI

end Arm
