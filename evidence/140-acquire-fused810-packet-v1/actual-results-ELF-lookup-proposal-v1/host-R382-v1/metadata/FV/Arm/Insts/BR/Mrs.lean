/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license; see third_party/NOTICE-lnsym.md.
-/
-- (FV addition, not in LNSym) MRS: move from a system register.
--
-- The only system register of the model is TPIDR_EL0, the EL0 thread pointer
-- (`StateField.TPIDR`; the loader / OS sets it, no instruction of the model writes it). The
-- backend emits only `mrs xt, tpidr_el0` (Cranelift's `0xd53bd040 | Rt`, in `tls_value`'s
-- local-exec sequence). Arm ARM (DDI 0487) "MRS" ASL, for TPIDR_EL0 (op0 = 0b11, i.e. o0 = 1;
-- op1 = 0b011, CRn = 0b1101, CRm = 0b0000, op2 = 0b010):
-- ```
-- X[t, 64] = TPIDR_EL0;
-- ```
-- (`X[31]` is XZR: the write is discarded.) Every other system register stops the machine
-- with an `Unimplemented` error, as the unimplemented hints do.

import FV.Arm.Decode.BR
import FV.Arm.Insts.Common

namespace Arm

/-- The `MRS` operands name TPIDR_EL0. -/
@[state_simp_rules]
def Mrs_cls.isTpidrEl0 (inst : Mrs_cls) : Prop :=
  inst.o0 = 1#1 ∧ inst.op1 = 0b011#3 ∧ inst.CRn = 0b1101#4 ∧ inst.CRm = 0b0000#4 ∧
    inst.op2 = 0b010#3

instance (inst : Mrs_cls) : Decidable (Mrs_cls.isTpidrEl0 inst) :=
  inferInstanceAs (Decidable (inst.o0 = 1#1 ∧ inst.op1 = 0b011#3 ∧ inst.CRn = 0b1101#4 ∧
    inst.CRm = 0b0000#4 ∧ inst.op2 = 0b010#3))

namespace BR

@[state_simp_rules]
def exec_mrs (inst : Mrs_cls) (s : ArmState) : ArmState :=
  if inst.isTpidrEl0 then
    let s := write_gpr_zr 64 inst.Rt (r StateField.TPIDR s) s
    let s := write_pc ((read_pc s) + 4#64) s
    s
  else
    write_err (StateError.Unimplemented s!"Unsupported {inst} encountered (system register)") s

end BR

end Arm
