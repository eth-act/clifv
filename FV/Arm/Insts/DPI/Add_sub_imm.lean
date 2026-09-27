/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
-- ADD, ADDS, SUB, SUBS (immediate): 32- and 64-bit versions

import FV.Arm.Decode
import FV.Arm.Insts.Common

namespace Arm


namespace DPI

open _root_.BitVec Arm.BitVec

@[state_simp_rules]
def exec_add_sub_imm (inst : Add_sub_imm_cls) (s : ArmState) : ArmState :=
    let sub_op        := inst.op = 1#1
    let setflags      := inst.S = 1#1
    let datasize      := if inst.sf = 1#1 then 64 else 32
    let imm           := 0#52 ++ inst.imm12
    let imm           := if inst.sh = 0#1 then
                          imm
                        else
                          imm <<< 12
    let operand1      := read_gpr datasize inst.Rn s
    let carryInAndOperand2
                      := if sub_op then
                          (1#1, ~~~imm)
                        else
                          (0#1, imm)
    -- `carry, operand2` is written as a let binding followed by strucure projections to
    -- work aroud a lean bug that desurgars `let (x, y) := if c then t else e` poorly:
    -- https://github.com/leanprover/lean4/issues/5388
    let carry := carryInAndOperand2.fst
    let operand2 := carryInAndOperand2.snd
    let operand2         := BitVec.zeroExtend datasize operand2
    let (result, pstate) := AddWithCarry operand1 operand2 carry
    -- State Updates
    let s'            := write_pc ((read_pc s) + 4#64) s
    let s'            := if setflags then write_pstate pstate s' else s'
    let s'            := if inst.Rd = 31#5 ∧ ¬ setflags
                         then write_gpr datasize inst.Rd result s'
                         else write_gpr_zr datasize inst.Rd result s'
    s'

----------------------------------------------------------------------

----------------------------------------------------------------------

end DPI

end Arm
