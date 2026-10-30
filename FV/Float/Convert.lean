/-
Conversions of the shared float core: `FPRoundInt`, `FPConvert` (with `FPConvertNaN`),
`FPToFixed`, `FixedToFP` (fbits = 0), and the exact truncation used by CLIF's trapping
`fcvt_to_{u,s}int` range checks (`docs/contracts/float.md`).
-/
import FV.Float.Round

namespace IEEE

/-- `FPRoundInt(op, fpcr, rounding, exact = FALSE)`: round to an integral value in the same
format; zero results keep the operand's sign. -/
def roundInt (f : Fmt) (rm : RMode) (op : Bits f) : Bits f :=
  let (t, s, m, e) := unpack f op
  if t = .snan ∨ t = .qnan then processNaN f t op
  else if t = .infinity then infinity f s
  else if t = .zero then zero f s
  else
    let i := roundToInt rm (signed s m) e
    if i = 0 then zero f s else round f .rz (i < 0) i.natAbs 0

/-- `FPConvertNaN`: keep the sign and the payload below the quiet bit, aligned at the top of
the destination fraction (truncated when narrowing), and set the quiet bit. -/
def convertNaN (src dst : Fmt) (op : Bits src) : Bits dst :=
  let payload := fracOf src op % 2 ^ (src.F - 1)
  let payload :=
    if src.F ≤ dst.F then payload * 2 ^ (dst.F - src.F) else payload / 2 ^ (src.F - dst.F)
  pack dst (signOf src op) dst.expOnes (2 ^ (dst.F - 1) + payload)

/-- `FPConvert(op, fpcr, rounding)` from `src` to `dst` (FZ = DN = AHP = 0). -/
def convert (src dst : Fmt) (rm : RMode) (op : Bits src) : Bits dst :=
  let (t, s, m, e) := unpack src op
  if t = .snan ∨ t = .qnan then convertNaN src dst op
  else if t = .infinity then infinity dst s
  else if t = .zero then zero dst s
  else round dst rm s m e

/-- `SatQ(i, M, unsigned)` without the saturation flag. -/
def satQ (i : Int) (M : Nat) (unsigned : Bool) : BitVec M :=
  if unsigned then
    if i < 0 then 0 else if (2 ^ M : Nat) ≤ i then BitVec.allOnes M else BitVec.ofInt M i
  else
    if i < -((2 ^ (M - 1) : Nat) : Int) then BitVec.ofInt M (-((2 ^ (M - 1) : Nat) : Int))
    else if ((2 ^ (M - 1) : Nat) : Int) ≤ i then BitVec.ofNat M (2 ^ (M - 1) - 1)
    else BitVec.ofInt M i

/-- `FPToFixed(op, fbits = 0, unsigned, fpcr, rounding, M)`: round to an integer and
saturate; NaN gives 0 (its `FPUnpack` value is `0.0`), ±∞ saturate. -/
def toFixed (f : Fmt) (op : Bits f) (unsigned : Bool) (M : Nat) (rm : RMode) : BitVec M :=
  let (t, s, m, e) := unpack f op
  if t = .infinity then satQ (signed s (2 ^ M)) M unsigned
  else satQ (roundToInt rm (signed s m) e) M unsigned

/-- `FixedToFP(op, fbits = 0, unsigned, fpcr, rounding)`: exact zero is `+0`. -/
def fromFixed (f : Fmt) (M : Nat) (x : BitVec M) (unsigned : Bool) (rm : RMode) : Bits f :=
  let i : Int := if unsigned then x.toNat else x.toInt
  if i = 0 then zero f false else round f rm (i < 0) i.natAbs 0

/-- The exact value of a finite operand truncated toward zero; `none` for NaNs and infinities. -/
def truncInt? (f : Fmt) (a : Bits f) : Option Int :=
  let (t, s, m, e) := unpack f a
  if t.isNaN ∨ t = .infinity then none
  else
    let n := if 0 ≤ e then m * 2 ^ e.toNat else m / 2 ^ (-e).toNat
    some (signed s n)

end IEEE
