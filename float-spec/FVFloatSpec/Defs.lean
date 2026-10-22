import FV.Float
import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Directed.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.RoundDyadicImpl.Proof
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Proof

/-!
# The link between `FV/Float` and FloatLib

`FV/Float` (namespace `IEEE`) is clifv's float semantics: a transcription of the Arm ARM
pseudocode on bit patterns, core Lean only. This library (`FVFloatSpec`, the only part of clifv
that imports FloatLib and hence Mathlib; nothing in `FV` imports it) proves those definitions
equal to FloatLib's IEEE 754 binary operations (`FloatLib.Floats.Formats.BinaryInterchange.Model`),
whose correctness against real-valued IEEE 754 rounding is proved in FloatLib
(`docs/contracts/float.md`, "Trust").

This file: FloatLib's descriptor of an `IEEE.Fmt`, the bit-preserving conversions `toM`/`ofM`,
and the rounding-mode correspondence.
-/

namespace IEEE.Spec

open FloatLib.Floats.Formats.BinaryInterchange

/-- The rounding modes `FPCR.RMode` selects, as FloatLib's `IEEERoundingMode`. -/
abbrev Mode := Model.IEEERoundingMode

/-- A FloatLib rounding mode as the `FPRounding` value the Arm pseudocode uses. -/
def _root_.FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode.asl :
    Mode → RMode
  | .nearestEven => .rne
  | .towardZero => .rz
  | .towardPositiveInfinity => .rpi
  | .towardNegativeInfinity => .rmi

/-- The layouts FloatLib describes: at least two exponent bits and one fraction bit. -/
structure FmtOk (f : Fmt) : Prop where
  E2 : 2 ≤ f.E
  F1 : 0 < f.F

theorem FmtOk.b32 : FmtOk .b32 := ⟨by decide, by decide⟩
theorem FmtOk.b64 : FmtOk .b64 := ⟨by decide, by decide⟩

/-- FloatLib's descriptor of a format: IEEE bias and encoding (`FloatFormat.ieee E F`). -/
def fl (f : Fmt) (h : FmtOk f) : FloatFormat := FloatFormat.ieee f.E f.F h.E2 h.F1

theorem fl_b32 : fl .b32 FmtOk.b32 = FloatFormat.binary32 := by decide
theorem fl_b64 : fl .b64 FmtOk.b64 = FloatFormat.binary64 := by decide

/-- An encoding as a FloatLib value (the same bits). -/
def toM (f : Fmt) (h : FmtOk f) (x : Bits f) : Model (fl f h) := Model.ofBits x

/-- A FloatLib value as an encoding (the same bits). -/
def ofM (f : Fmt) (h : FmtOk f) (y : Model (fl f h)) : Bits f := y.bits

@[simp] theorem ofM_toM (f : Fmt) (h : FmtOk f) (x : Bits f) : ofM f h (toM f h x) = x := rfl
@[simp] theorem toM_ofM (f : Fmt) (h : FmtOk f) (y : Model (fl f h)) : toM f h (ofM f h y) = y :=
  rfl

end IEEE.Spec
