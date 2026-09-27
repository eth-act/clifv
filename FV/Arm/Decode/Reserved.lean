/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license as described in third_party/lnsym-upstream/LICENSE.
-/
-- (FV addition, not in LNSym) The A64 "Reserved" encoding group (`op0 = 0`, `op1 = 0000`):
-- only `UDF #imm16` (permanently undefined) is allocated there.
import FV.Arm.BitVec

namespace Arm

------------------------------------------------------------------------------

section Decode

open _root_.BitVec Arm.BitVec

/-- `UDF #imm16`: bits 31:16 are all zero. -/
structure Udf_cls where
  _fixed : BitVec 16 := 0#16 -- [31:16]
  imm16  : BitVec 16         -- [15:0]
deriving DecidableEq, Repr

instance : ToString Udf_cls where toString a := toString (repr a)

def Udf_cls.toBitVec32 (x : Udf_cls) : BitVec 32 :=
  x._fixed ++ x.imm16

inductive ReservedInst where
  | Udf :
    Udf_cls → ReservedInst
deriving DecidableEq, Repr

instance : ToString ReservedInst where toString a := toString (repr a)

end Decode

end Arm
