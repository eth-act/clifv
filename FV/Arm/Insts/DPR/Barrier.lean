/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license; see third_party/NOTICE-lnsym.md.
-/
-- (FV addition, not in LNSym) Barriers: DMB/DSB/ISB.
--
-- The backend emits only `dmb ish` (`MInst.Fence`, Cranelift `enc_dmb_ish`). In the
-- single-threaded model a barrier is a no-op (it orders memory accesses of other agents,
-- which the model does not have).

import FV.Arm.Decode
import FV.Arm.Insts.Common

namespace Arm

namespace DPR

/-- A barrier does not change the architectural state (single-threaded model). -/
@[state_simp_rules]
def exec_barrier (inst : Barrier_cls) (s : ArmState) : ArmState :=
  write_pc ((read_pc s) + 4#64) s

end DPR

end Arm
