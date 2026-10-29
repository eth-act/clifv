/-
Root of the shared IEEE 754 core (`namespace IEEE`, `docs/contracts/float.md`): binary32 and
binary64 as the Arm ARM pseudocode defines them with FPCR = 0 except the rounding mode. Used by
both the CLIF float semantics and the Arm FP instructions.
-/
module

public import FV.Float.Basic
public import FV.Float.Round
public import FV.Float.Arith
public import FV.Float.Convert

public section
