/-
`FPRound` / `FPRoundBase` (FZ = 0, AHP = 0) and the integer rounding step shared by
`FPRoundInt` and `FPToFixed`, on exact values `mant * 2^exp` (`docs/contracts/float.md`).
-/
module

public import FV.Float.Basic

public section

namespace IEEE

/-- Floor square root by Newton's iteration from the overestimate `2^(log2 n / 2 + 1)`; each
step at least halves the distance to `√n`, so `log2 n + 4` steps reach the fixed point. -/
@[expose] def isqrt (n : Nat) : Nat :=
  if n = 0 then 0 else go (n.log2 + 4) n (2 ^ (n.log2 / 2 + 1))
where
  go : Nat → Nat → Nat → Nat
    | 0, _, x => x
    | fuel + 1, n, x =>
      let y := (x + n / x) / 2
      if y < x then go fuel n y else x

@[expose] section
@[expose] section
/-- The rounding error of a truncated value in units of the last kept place: exactly zero,
in `(0, ½)`, exactly `½`, or in `(½, 1)`. -/
inductive Err
  | exact | low | half | high
  deriving DecidableEq, Repr
end
end

/-- `mant / 2^s` (`s > 0`) truncated, with the error class; `sticky` means the true value lies
strictly between `mant` and `mant + 1` (a nonzero discarded tail below `mant`'s last bit). -/
@[expose] def truncShift (mant s : Nat) (sticky : Bool) : Nat × Err :=
  let r := mant % 2 ^ s
  let half := 2 ^ (s - 1)
  (mant / 2 ^ s,
    if r = 0 ∧ !sticky then .exact
    else if r < half then .low
    else if r = half ∧ !sticky then .half
    else .high)

/-- `FPRoundBase(op, fpcr, rounding)` with FZ = 0, AHP = 0 for a nonzero value
`(-1)^sign * (mant + δ) * 2^exp`, where `δ = 0` if `!sticky` and `0 < δ < 1` otherwise.
Requirement when `sticky`: `mant ≥ 2^(F+1)`, so the unknown tail lies below the rounding
position (callers `div` and `sqrt` provide `F + 3` bits). `mant = 0` (excluded by the ASL's
`assert op != 0.0`) yields a signed zero. Overflow gives ∞ or the largest finite number
depending on the mode; tiny results are rounded gradually to denormals. -/
@[expose] def round (f : Fmt) (rm : RMode) (sign : Bool) (mant : Nat) (exp : Int)
    (sticky : Bool := false) : Bits f :=
  if mant = 0 then zero f sign else
  -- `exponent`: the unbiased exponent of the value, `2^exponent ≤ |value| < 2^(exponent+1)`.
  let exponent : Int := (mant.log2 : Int) + exp
  let biased : Int := max (exponent - f.minExp + 1) 0
  -- Exponent of the last kept place: `F` places below the leading bit, or the denormal ulp.
  let ulp : Int := (if biased = 0 then f.minExp else exponent) - f.F
  let s : Int := ulp - exp
  let (intMant, err) : Nat × Err :=
    if s ≤ 0 then (mant * 2 ^ (-s).toNat, if sticky then .low else .exact)
    else truncShift mant s.toNat sticky
  let inexact := err ≠ .exact
  let (roundUp, overflowToInf) : Bool × Bool :=
    match rm with
    | .rne => (err = .high ∨ (err = .half ∧ intMant % 2 = 1), true)
    | .rna => (err = .high ∨ err = .half, true)
    | .rpi => (inexact ∧ !sign, !sign)
    | .rmi => (inexact ∧ sign, sign)
    | .rz => (false, false)
  let (intMant, biased) : Nat × Int :=
    if roundUp then
      let m := intMant + 1
      let b : Int := if m = 2 ^ f.F then 1 else biased
      if m = 2 ^ (f.F + 1) then (m / 2, b + 1) else (m, b)
    else (intMant, biased)
  if (f.expOnes : Int) ≤ biased then
    if overflowToInf then infinity f sign else maxNormal f sign
  else pack f sign biased.toNat (intMant % 2 ^ f.F)

/-- The integer rounding step of `FPRoundInt` / `FPToFixed` (fbits = 0): `RoundDown` of the
signed value `v * 2^exp`, then the mode's increment. -/
@[expose] def roundToInt (rm : RMode) (v : Int) (exp : Int) : Int :=
  if 0 ≤ exp then v * (2 ^ exp.toNat : Nat) else
  let d : Int := (2 ^ (-exp).toNat : Nat)
  let intResult := v / d          -- floor division (`Int.div` rounds toward −∞ for `d > 0`)
  let r := v % d                  -- `error = r / d ∈ [0, 1)`
  let roundUp : Bool :=
    match rm with
    | .rne => 2 * r > d ∨ (2 * r = d ∧ intResult % 2 = 1)
    | .rpi => r ≠ 0
    | .rmi => false
    | .rz => r ≠ 0 ∧ intResult < 0
    | .rna => 2 * r > d ∨ (2 * r = d ∧ 0 ≤ intResult)
  if roundUp then intResult + 1 else intResult

/-- The signed exact value `(-1)^sign * mant` as an integer. -/
@[expose] def signed (sign : Bool) (mant : Nat) : Int := if sign then -(mant : Int) else mant

end IEEE
