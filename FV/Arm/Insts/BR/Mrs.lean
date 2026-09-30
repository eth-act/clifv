/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license; see third_party/NOTICE-lnsym.md.
-/
-- (FV addition, not in LNSym) MRS: move from a system register.
--
-- The backend emits only `mrs xt, tpidr_el0` (the thread pointer, in `tls_value`'s TLSDESC
-- sequence, which is outside every theorem). The model has no system registers, so the
-- instruction stops the machine with an error, as the unimplemented hints do.

import FV.Arm.Decode
import FV.Arm.Insts.Common

namespace Arm

namespace BR

@[state_simp_rules]
def exec_mrs (inst : Mrs_cls) (s : ArmState) : ArmState :=
  write_err (StateError.Unimplemented s!"Unsupported {inst} encountered (no system registers)") s

end BR

end Arm
