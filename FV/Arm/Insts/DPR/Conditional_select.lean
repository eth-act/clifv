/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
-- CSEL, CSINC, CSINV, CSNEG: 32- and 64-bit versions
-- Modified by fv-compiler-rust (2026): ported to Lean v4.34.1, module prefix FV.Arm, wrapped in
-- namespace Arm; upstream implemented only CSEL, CSINC/CSINV/CSNEG (and so the aliases CSET,
-- CSETM, CINC, CINV, CNEG) added from the Arm ARM (DDI 0487) ASL shared by the
-- "Conditional select" encodings:
--   boolean else_inv = (op == '1'); boolean else_inc = (o2 == '1');
--   if ConditionHolds(cond) then result = X[n, datasize];
--   else result = X[m, datasize];
--        if else_inv then result = NOT(result);
--        if else_inc then result = result + 1;
--   X[d, datasize] = result;
-- Unallocated: S == '1' or op2<1> == '1'. Cross-checked against VeriISLE
-- `MInst.CSel`/`CSNeg`/`CSet`/`CSetm` (cranelift/codegen/src/isa/aarch64/spec/conds.isle).

import FV.Arm.Decode
import FV.Arm.State
import FV.Arm.Insts.Common
import FV.Arm.BitVec

namespace Arm


namespace DPR

open _root_.BitVec Arm.BitVec

@[state_simp_rules]
def exec_conditional_select (inst : Conditional_select_cls) (s : ArmState) : ArmState :=
    let datasize := if inst.sf = 1#1 then 64 else 32
    if inst.S = 1#1 ∨ lsb inst.op2 1 = 1#1 then
      write_err
        (StateError.Illegal
          s!"Illegal DPR.Conditional_select_cls {inst} encountered in exec_inst!")
      s
    else
      let else_inv := inst.op = 1#1
      let else_inc := lsb inst.op2 0 = 1#1
      let result :=
        if ConditionHolds inst.cond s then
          read_gpr_zr datasize inst.Rn s
        else
          let result := read_gpr_zr datasize inst.Rm s
          let result := if else_inv then ~~~result else result
          if else_inc then result + 1#datasize else result
      -- State Updates
      let s            := write_pc ((read_pc s) + 4#64) s
      let s            := write_gpr_zr datasize inst.Rd result s
      s

----------------------------------------------------------------------

end DPR

end Arm
