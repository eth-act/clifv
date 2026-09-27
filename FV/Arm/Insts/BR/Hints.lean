/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/
-- NOP, CSDB, BTI
-- Modified by fv-compiler-rust (2026): ported to Lean v4.34.1, module prefix FV.Arm, wrapped in
-- namespace Arm; CSDB (HINT #20) and BTI {c,j,jc} (HINT #32/#34/#36/#38) added. Both only
-- advance the PC in this model, following the Arm ARM (DDI 0487) ASL:
--   CSDB: `ConsumptionOfSpeculativeDataBarrier();` -- a speculation barrier; the model has no
--         speculation, so it has no architectural effect.
--   BTI:  `SystemHintOp_BTI` raises a Branch Target exception only when executed with a
--         non-zero `PSTATE.BTYPE` on a guarded page. The model has no guarded pages
--         (`GPx = 0`), so BTI behaves as a NOP. Cranelift emits these only with
--         `use_csdb`/`use_bti`, which the pinned settings leave off.
-- Other hints (PACIASP/AUTIASP, YIELD, WFE, ...) stay unimplemented.

import FV.Arm.Decode
import FV.Arm.Insts.Common

namespace Arm


----------------------------------------------------------------------

namespace BR

open _root_.BitVec Arm.BitVec

@[state_simp_rules]
def exec_hints (inst : Hints_cls) (s : ArmState) : ArmState :=
  if (inst.CRm = 0b0000#4 ∧ inst.op2 = 0b000#3) ∨     -- NOP
     (inst.CRm = 0b0010#4 ∧ inst.op2 = 0b100#3) ∨     -- CSDB
     (inst.CRm = 0b0100#4 ∧ lsb inst.op2 0 = 0#1) then -- BTI, BTI c, BTI j, BTI jc
    write_pc ((read_pc s) + 4#64) s
  else
    write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s

end BR

end Arm
