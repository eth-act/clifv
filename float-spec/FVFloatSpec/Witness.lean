import FVFloatSpec.Arith
import FVFloatSpec.Div
import FVFloatSpec.Sqrt
import FVFloatSpec.Convert
import FVFloatSpec.Compare

/-!
# Witnesses for the `FVFloatSpec` theorems

The equalities hold for every input; these instances check concrete cases with the kernel on
both sides (`decide +kernel`), so the FloatLib side is not vacuous: it computes the IEEE results.
-/

namespace IEEE.Spec.Witness

open IEEE IEEE.Spec FloatLib.Floats.Formats.BinaryInterchange

-- 0.1 + 0.2 = 0.30000000000000004 (binary64), FloatLib's addition and the Arm one
example : (ofM .b64 FmtOk.b64 (Model.addWithRounding .nearestEven
    (toM .b64 FmtOk.b64 0x3FB999999999999A#64) (toM .b64 FmtOk.b64 0x3FC999999999999A#64))) =
    0x3FD3333333333334#64 := by decide +kernel
example : IEEE.add .b64 (Model.IEEERoundingMode.asl .nearestEven) 0x3FB999999999999A#64 0x3FC999999999999A#64 =
    ofM .b64 FmtOk.b64 (Model.addWithRounding .nearestEven
      (toM .b64 FmtOk.b64 0x3FB999999999999A#64) (toM .b64 FmtOk.b64 0x3FC999999999999A#64)) :=
  add_eq_b64 _ _ _

-- 1 + 2^-24 (binary32) toward +∞ rounds up
example : (ofM .b32 FmtOk.b32 (Model.addWithRounding .towardPositiveInfinity
    (toM .b32 FmtOk.b32 0x3F800000#32) (toM .b32 FmtOk.b32 0x33800000#32))) = 0x3F800001#32 := by
  decide +kernel

-- 1/3 (binary64)
example : (ofM .b64 FmtOk.b64 (Model.divWithRounding .nearestEven
    (toM .b64 FmtOk.b64 0x3FF0000000000000#64) (toM .b64 FmtOk.b64 0x4008000000000000#64))) =
    0x3FD5555555555555#64 := by decide +kernel

-- sqrt 2 (binary64)
example : (ofM .b64 FmtOk.b64 (Model.sqrtWithRounding .nearestEven
    (toM .b64 FmtOk.b64 0x4000000000000000#64))) = 0x3FF6A09E667F3BCD#64 := by decide +kernel

-- ∞ - ∞ is the default NaN on both sides
example : (ofM .b32 FmtOk.b32 (Model.subWithRounding .nearestEven
    (toM .b32 FmtOk.b32 0x7F800000#32) (toM .b32 FmtOk.b32 0x7F800000#32))) = 0x7FC00000#32 := by
  decide +kernel

end IEEE.Spec.Witness
