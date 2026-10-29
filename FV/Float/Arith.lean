/-
Arithmetic of the shared float core: `FPAdd`, `FPSub`, `FPMul`, `FPDiv`, `FPSqrt`, `FPMulAdd`,
`FPMax`, `FPMin`, `FPCompare` (`docs/contracts/float.md`). FPCR = 0 except the rounding mode.
-/
module

public import FV.Float.Round

public section

namespace IEEE

/-- Round the exact signed value `m * 2^e`; an exact zero sum gets the sign the ASL gives
it (`-0` iff rounding toward −∞). -/
def roundSum (f : Fmt) (rm : RMode) (m : Int) (e : Int) : Bits f :=
  if m = 0 then zero f (rm = .rmi) else round f rm (m < 0) m.natAbs e

/-- `(-1)^s1 m1 2^e1 + (-1)^s2 m2 2^e2` exactly, as `(m, min e1 e2)`. -/
def addExact (s1 : Bool) (m1 : Nat) (e1 : Int) (s2 : Bool) (m2 : Nat) (e2 : Int) : Int × Int :=
  let e := min e1 e2
  (signed s1 (m1 * 2 ^ (e1 - e).toNat) + signed s2 (m2 * 2 ^ (e2 - e).toNat), e)

/-- Order of two non-NaN unpacked operands by value (`FPUnpack` gives infinities the value
`±2^1000000`; zeros of either sign are equal). -/
def cmpVal (t1 : FPType) (s1 : Bool) (m1 : Nat) (e1 : Int)
    (t2 : FPType) (s2 : Bool) (m2 : Nat) (e2 : Int) : Ordering :=
  match t1 == .infinity, t2 == .infinity with
  | true, true => if s1 = s2 then .eq else if s1 then .lt else .gt
  | true, false => if s1 then .lt else .gt
  | false, true => if s2 then .gt else .lt
  | false, false =>
    let (d, _) := addExact s1 m1 e1 (!s2) m2 e2
    if d < 0 then .lt else if d = 0 then .eq else .gt

/-- `FPAdd(op1, op2, fpcr)`. -/
def add (f : Fmt) (rm : RMode) (op1 op2 : Bits f) : Bits f :=
  let (t1, s1, m1, e1) := unpack f op1
  let (t2, s2, m2, e2) := unpack f op2
  match processNaNs f t1 t2 op1 op2 with
  | some r => r
  | none =>
    let inf1 := t1 = .infinity; let inf2 := t2 = .infinity
    let zero1 := t1 = .zero; let zero2 := t2 = .zero
    if inf1 ∧ inf2 ∧ s1 = !s2 then defaultNaN f
    else if (inf1 ∧ !s1) ∨ (inf2 ∧ !s2) then infinity f false
    else if (inf1 ∧ s1) ∨ (inf2 ∧ s2) then infinity f true
    else if zero1 ∧ zero2 ∧ s1 = s2 then zero f s1
    else
      let (m, e) := addExact s1 m1 e1 s2 m2 e2
      roundSum f rm m e

/-- `FPSub(op1, op2, fpcr)`. -/
def sub (f : Fmt) (rm : RMode) (op1 op2 : Bits f) : Bits f :=
  let (t1, s1, m1, e1) := unpack f op1
  let (t2, s2, m2, e2) := unpack f op2
  match processNaNs f t1 t2 op1 op2 with
  | some r => r
  | none =>
    let inf1 := t1 = .infinity; let inf2 := t2 = .infinity
    let zero1 := t1 = .zero; let zero2 := t2 = .zero
    if inf1 ∧ inf2 ∧ s1 = s2 then defaultNaN f
    else if (inf1 ∧ !s1) ∨ (inf2 ∧ s2) then infinity f false
    else if (inf1 ∧ s1) ∨ (inf2 ∧ !s2) then infinity f true
    else if zero1 ∧ zero2 ∧ s1 = !s2 then zero f s1
    else
      let (m, e) := addExact s1 m1 e1 (!s2) m2 e2
      roundSum f rm m e

/-- `FPMul(op1, op2, fpcr)`. -/
def mul (f : Fmt) (rm : RMode) (op1 op2 : Bits f) : Bits f :=
  let (t1, s1, m1, e1) := unpack f op1
  let (t2, s2, m2, e2) := unpack f op2
  match processNaNs f t1 t2 op1 op2 with
  | some r => r
  | none =>
    let inf1 := t1 = .infinity; let inf2 := t2 = .infinity
    let zero1 := t1 = .zero; let zero2 := t2 = .zero
    if (inf1 ∧ zero2) ∨ (zero1 ∧ inf2) then defaultNaN f
    else if inf1 ∨ inf2 then infinity f (s1 != s2)
    else if zero1 ∨ zero2 then zero f (s1 != s2)
    else round f rm (s1 != s2) (m1 * m2) (e1 + e2)

/-- `FPDiv(op1, op2, fpcr)`. The quotient is computed with at least `F + 3` bits and a sticky
bit for a nonzero remainder. -/
def div (f : Fmt) (rm : RMode) (op1 op2 : Bits f) : Bits f :=
  let (t1, s1, m1, e1) := unpack f op1
  let (t2, s2, m2, e2) := unpack f op2
  match processNaNs f t1 t2 op1 op2 with
  | some r => r
  | none =>
    let inf1 := t1 = .infinity; let inf2 := t2 = .infinity
    let zero1 := t1 = .zero; let zero2 := t2 = .zero
    if (inf1 ∧ inf2) ∨ (zero1 ∧ zero2) then defaultNaN f
    else if inf1 ∨ zero2 then infinity f (s1 != s2)
    else if zero1 ∨ inf2 then zero f (s1 != s2)
    else
      -- `m1 * 2^k / m2 ≥ 2^(F+3)` for `k = F + 3 + log2 m2 + 1`.
      let k := f.F + 4 + m2.log2
      let n := m1 * 2 ^ k
      round f rm (s1 != s2) (n / m2) (e1 - e2 - k) (n % m2 ≠ 0)

/-- `FPSqrt(op, fpcr)`. The root is computed with at least `F + 3` bits and a sticky bit for an
inexact root. -/
@[expose] def sqrt (f : Fmt) (rm : RMode) (op : Bits f) : Bits f :=
  let (t, s, m, e) := unpack f op
  if t = .snan ∨ t = .qnan then processNaN f t op
  else if t = .zero then zero f s
  else if t = .infinity ∧ !s then infinity f s
  else if s then defaultNaN f
  else
    -- Make the exponent even, then scale by `4^(F+3)`: `isqrt n ≥ 2^(F+3)`.
    let (m, e) : Nat × Int := if e % 2 = 0 then (m, e) else (2 * m, e - 1)
    let n := m * 4 ^ (f.F + 3)
    let r := isqrt n
    round f rm false r (e / 2 - (f.F + 3 : Nat)) (r * r ≠ n)

/-- `FPMulAdd(addend, op1, op2, fpcr)`: `addend + op1 * op2` with a single rounding. -/
def mulAdd (f : Fmt) (rm : RMode) (addend op1 op2 : Bits f) : Bits f :=
  let (tA, sA, mA, eA) := unpack f addend
  let (t1, s1, m1, e1) := unpack f op1
  let (t2, s2, m2, e2) := unpack f op2
  let inf1 := t1 = .infinity; let zero1 := t1 = .zero
  let inf2 := t2 = .infinity; let zero2 := t2 = .zero
  let nan := processNaNs3 f tA t1 t2 addend op1 op2
  -- A quiet-NaN addend does not hide the invalid product `0 * ∞`.
  if tA = .qnan ∧ ((inf1 ∧ zero2) ∨ (zero1 ∧ inf2)) then defaultNaN f else
  match nan with
  | some r => r
  | none =>
    let infA := tA = .infinity; let zeroA := tA = .zero
    let signP := s1 != s2
    let infP := inf1 ∨ inf2
    let zeroP := zero1 ∨ zero2
    if (inf1 ∧ zero2) ∨ (zero1 ∧ inf2) ∨ (infA ∧ infP ∧ sA ≠ signP) then defaultNaN f
    else if (infA ∧ !sA) ∨ (infP ∧ !signP) then infinity f false
    else if (infA ∧ sA) ∨ (infP ∧ signP) then infinity f true
    else if zeroA ∧ zeroP ∧ sA = signP then zero f sA
    else
      let (m, e) := addExact sA mA eA signP (m1 * m2) (e1 + e2)
      roundSum f rm m e

/-- `FPMax(op1, op2, fpcr)` (AH = 0, `altfp = FALSE`): NaN-propagating, `max(-0, +0) = +0`. -/
@[expose] def max (f : Fmt) (rm : RMode) (op1 op2 : Bits f) : Bits f :=
  let (t1, s1, m1, e1) := unpack f op1
  let (t2, s2, m2, e2) := unpack f op2
  match processNaNs f t1 t2 op1 op2 with
  | some r => r
  | none =>
    let (t, s, m, e) :=
      if cmpVal t1 s1 m1 e1 t2 s2 m2 e2 = .gt then (t1, s1, m1, e1) else (t2, s2, m2, e2)
    if t = .infinity then infinity f s
    else if t = .zero then zero f (s1 && s2)
    else round f rm s m e

/-- `FPMin(op1, op2, fpcr)` (AH = 0, `altfp = FALSE`): NaN-propagating, `min(-0, +0) = -0`. -/
def min (f : Fmt) (rm : RMode) (op1 op2 : Bits f) : Bits f :=
  let (t1, s1, m1, e1) := unpack f op1
  let (t2, s2, m2, e2) := unpack f op2
  match processNaNs f t1 t2 op1 op2 with
  | some r => r
  | none =>
    let (t, s, m, e) :=
      if cmpVal t1 s1 m1 e1 t2 s2 m2 e2 = .lt then (t1, s1, m1, e1) else (t2, s2, m2, e2)
    if t = .infinity then infinity f s
    else if t = .zero then zero f (s1 || s2)
    else round f rm s m e

/-- `FPCompare(op1, op2, signal_nans, fpcr)` without the exception side effect. -/
def compare (f : Fmt) (op1 op2 : Bits f) : Cmp :=
  let (t1, s1, m1, e1) := unpack f op1
  let (t2, s2, m2, e2) := unpack f op2
  if t1.isNaN ∨ t2.isNaN then .un
  else match cmpVal t1 s1 m1 e1 t2 s2 m2 e2 with
    | .lt => .lt
    | .eq => .eq
    | .gt => .gt

end IEEE
