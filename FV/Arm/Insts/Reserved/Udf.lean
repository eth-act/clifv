/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license; see third_party/NOTICE-lnsym.md.
-/
-- (FV addition, not in LNSym) UDF #imm16.
--
-- Arm ARM (DDI 0487) "UDF" ASL:
--
--   // The imm16 field is ignored by hardware.
--   UNDEFINED;
--
-- UNDEFINED raises an Undefined Instruction exception at the address of the `UDF`; Linux
-- delivers `SIGILL` with the PC still pointing at it. The model stops with the distinguished
-- error `StateError.Trap imm16` and leaves every other part of the state (including the PC)
-- unchanged, so `stepi` (and hence `run`) makes no further progress. Cranelift lowers every
-- CLIF `trap` / trap-guarded check to `udf #0xc11f` (`Inst::TRAP_OPCODE`); the trap code itself
-- is only in Cranelift's side table, so `imm16` does not identify it.

import FV.Arm.Decode
import FV.Arm.Insts.Common

namespace Arm

namespace Reserved

open _root_.BitVec Arm.BitVec

@[state_simp_rules]
def exec_udf (inst : Udf_cls) (s : ArmState) : ArmState :=
  write_err (StateError.Trap inst.imm16) s

@[state_simp_rules]
def exec_reserved (inst : ReservedInst) (s : ArmState) : ArmState :=
  match inst with
  | ReservedInst.Udf i => exec_udf i s

end Reserved

end Arm
