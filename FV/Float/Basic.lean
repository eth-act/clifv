/-
IEEE 754 binary formats for the shared float core (`docs/contracts/float.md`).

Bit-precise and kernel-reducible: every function is closed-form `Nat`/`Int` arithmetic or
structural recursion on fuel, so `decide +kernel` evaluates concrete cases. The functions are
transcriptions of the Arm ARM pseudocode (`shared/functions/float/*`) with `FPCR` fixed to the
Linux default (`AHP = DN = FZ = FZ16 = AH = 0`) and the rounding mode passed explicitly; the
cumulative exception flags (`FPSR`) are not modelled.

This file: formats, `FPUnpack`, the constant encodings (`FPZero`, `FPInfinity`, `FPMaxNormal`,
`FPDefaultNaN`), `FPProcessNaN(s)`, `FPNeg`, `FPAbs`.
-/

module

public section

namespace IEEE

@[expose] section
@[expose] section
/-- A binary interchange format: `E` exponent bits, `F` fraction bits (width `1 + E + F`).
Assumes `E ≥ 2` and `F ≥ 1`. -/
structure Fmt where
  E : Nat
  F : Nat
  deriving DecidableEq, Repr
end
end

/-- binary32 (`f32`). -/
abbrev Fmt.b32 : Fmt := ⟨8, 23⟩
/-- binary64 (`f64`). -/
abbrev Fmt.b64 : Fmt := ⟨11, 52⟩

/-- The total width `1 + E + F`. -/
abbrev Fmt.N (f : Fmt) : Nat := 1 + f.E + f.F

/-- The encodings of a format; `Bits .b32` is defeq to `BitVec 32`, `Bits .b64` to `BitVec 64`. -/
abbrev Bits (f : Fmt) := BitVec (1 + f.E + f.F)

/-- Exponent bias `2^(E-1) - 1`. -/
@[expose] def Fmt.bias (f : Fmt) : Nat := 2 ^ (f.E - 1) - 1

/-- Unbiased exponent of the smallest normal number (`minimum_exp` in `FPRoundBase`). -/
@[expose] def Fmt.minExp (f : Fmt) : Int := 1 - (f.bias : Int)

/-- The all-ones biased exponent (infinities and NaNs). -/
@[expose] def Fmt.expOnes (f : Fmt) : Nat := 2 ^ f.E - 1

@[expose] section
@[expose] section
/-- Rounding modes (`FPRounding`): to nearest ties to even, toward +∞, toward −∞, toward zero,
to nearest ties away from zero. `FPCR.RMode` selects one of the first four. -/
inductive RMode
  | rne | rpi | rmi | rz | rna
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- `FPType`. -/
inductive FPType
  | zero | denormal | nonzero | infinity | qnan | snan
  deriving DecidableEq, Repr, Inhabited
end
end

@[expose] section
@[expose] section
/-- Result of `FPCompare` (`NZCV` = `0110`, `1000`, `0010`, `0011`). -/
inductive Cmp
  | lt | eq | gt | un
  deriving DecidableEq, Repr, Inhabited
end
end

/-- `FPType` is a NaN. -/
@[expose] def FPType.isNaN : FPType → Bool
  | .qnan | .snan => true
  | _ => false

/-- Encode `sign : bexp : frac` (fields are taken modulo their widths by the caller). -/
@[expose] def pack (f : Fmt) (sign : Bool) (bexp frac : Nat) : Bits f :=
  BitVec.ofNat _ ((if sign then 2 ^ (f.E + f.F) else 0) + bexp * 2 ^ f.F + frac)

/-- The sign bit. -/
@[expose] def signOf (f : Fmt) (x : Bits f) : Bool := decide (2 ^ (f.E + f.F) ≤ x.toNat)

/-- The biased exponent field. -/
@[expose] def expOf (f : Fmt) (x : Bits f) : Nat := x.toNat / 2 ^ f.F % 2 ^ f.E

/-- The fraction field. -/
@[expose] def fracOf (f : Fmt) (x : Bits f) : Nat := x.toNat % 2 ^ f.F

/-- `FPUnpack` (FZ = 0): the class, the sign and the exact magnitude `mant * 2^exp` of a
zero, denormal or normal number (`mant = 0`, `exp = 0` for infinities and NaNs). -/
@[expose] def unpack (f : Fmt) (x : Bits f) : FPType × Bool × Nat × Int :=
  let sign := signOf f x
  let bexp := expOf f x
  let frac := fracOf f x
  if bexp = 0 then
    if frac = 0 then (.zero, sign, 0, 0)
    else (.denormal, sign, frac, f.minExp - f.F)
  else if bexp = f.expOnes then
    if frac = 0 then (.infinity, sign, 0, 0)
    else if 2 ^ (f.F - 1) ≤ frac then (.qnan, sign, 0, 0)
    else (.snan, sign, 0, 0)
  else (.nonzero, sign, 2 ^ f.F + frac, (bexp : Int) - f.bias - f.F)

/-- `FPZero(sign)`. -/
@[expose] def zero (f : Fmt) (sign : Bool) : Bits f := pack f sign 0 0

/-- `FPInfinity(sign)`. -/
@[expose] def infinity (f : Fmt) (sign : Bool) : Bits f := pack f sign f.expOnes 0

/-- `FPMaxNormal(sign)`. -/
@[expose] def maxNormal (f : Fmt) (sign : Bool) : Bits f := pack f sign (f.expOnes - 1) (2 ^ f.F - 1)

/-- `FPDefaultNaN` (AH = 0: positive sign, quiet bit only); `0x7FC00000` for binary32. -/
@[expose] def defaultNaN (f : Fmt) (sign : Bool := false) : Bits f :=
  pack f sign f.expOnes (2 ^ (f.F - 1))

/-- The class of an encoding. -/
@[expose] def typeOf (f : Fmt) (x : Bits f) : FPType := (unpack f x).1

@[expose] def isNaN (f : Fmt) (x : Bits f) : Bool := (typeOf f x).isNaN
def isSNaN (f : Fmt) (x : Bits f) : Bool := typeOf f x = .snan
def isQNaN (f : Fmt) (x : Bits f) : Bool := typeOf f x = .qnan
def isInf (f : Fmt) (x : Bits f) : Bool := typeOf f x = .infinity
def isZero (f : Fmt) (x : Bits f) : Bool := typeOf f x = .zero

/-- `FPProcessNaN` (DN = 0): a signalling NaN is quietened by setting the top fraction bit,
a quiet NaN is returned unchanged. -/
@[expose] def processNaN (f : Fmt) (t : FPType) (op : Bits f) : Bits f :=
  if t = .snan then op ||| BitVec.ofNat _ (2 ^ (f.F - 1)) else op

/-- `FPProcessNaNs`: `some` result (`done = TRUE`) iff an operand is a NaN; signalling NaNs
first, then quiet NaNs, each in operand order. -/
@[expose] def processNaNs (f : Fmt) (t1 t2 : FPType) (op1 op2 : Bits f) : Option (Bits f) :=
  if t1 = .snan then some (processNaN f t1 op1)
  else if t2 = .snan then some (processNaN f t2 op2)
  else if t1 = .qnan then some (processNaN f t1 op1)
  else if t2 = .qnan then some (processNaN f t2 op2)
  else none

/-- `FPProcessNaNs3`. -/
@[expose] def processNaNs3 (f : Fmt) (t1 t2 t3 : FPType) (op1 op2 op3 : Bits f) : Option (Bits f) :=
  if t1 = .snan then some (processNaN f t1 op1)
  else if t2 = .snan then some (processNaN f t2 op2)
  else if t3 = .snan then some (processNaN f t3 op3)
  else if t1 = .qnan then some (processNaN f t1 op1)
  else if t2 = .qnan then some (processNaN f t2 op2)
  else if t3 = .qnan then some (processNaN f t3 op3)
  else none

/-- `FPNeg` (AH = 0): flip the sign bit, also of NaNs. -/
@[expose] def neg (f : Fmt) (a : Bits f) : Bits f := a ^^^ BitVec.ofNat _ (2 ^ (f.E + f.F))

/-- `FPAbs` (AH = 0): clear the sign bit, also of NaNs. -/
@[expose] def abs (f : Fmt) (a : Bits f) : Bits f := a &&& BitVec.ofNat _ (2 ^ (f.E + f.F) - 1)

end IEEE
