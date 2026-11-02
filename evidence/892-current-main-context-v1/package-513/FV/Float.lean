/-
Root of the shared IEEE 754 core (`namespace IEEE`, `docs/contracts/float.md`): binary32 and
binary64 as the Arm ARM pseudocode defines them with FPCR = 0 except the rounding mode. Used by
both the CLIF float semantics and the Arm FP instructions.
-/
import FV.Float.Basic
import FV.Float.Round
import FV.Float.Arith
import FV.Float.Convert
