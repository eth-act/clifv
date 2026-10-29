module

public section

/-!
# CLIF float literals (`Ieee32`/`Ieee64` text)

The text form of `f32const`/`f64const` immediates and of float run-line values, as Cranelift
0.136.1's `parse_float`/`format_float` (`cranelift/codegen/src/ir/immediates.rs`) define it:
hexadecimal significand with a binary exponent (`0x1.8p3`, `-0x0.0004p-126`), the decimal zero
`0.0`, `Inf`, `NaN` (canonical quiet NaN), `NaN:0xT` (quiet NaN with payload `T`) and `sNaN:0xT`,
each with an optional sign. Literals are exact: a value that needs rounding is an error, as in
Cranelift. `w`/`t` are the exponent and trailing-significand field widths (8/23, 11/52).
-/

namespace Clif.FloatLit

/-- Value of a hexadecimal digit. -/
@[expose] def hexDigit? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Hexadecimal natural number (no prefix, at least one digit). -/
@[expose] def parseHexNat? (s : String) : Option Nat :=
  if s.isEmpty then none else
  s.toList.foldlM (init := 0) fun acc c => (hexDigit? c).map (acc * 16 + ·)

/-- Decimal integer with an optional sign. -/
@[expose] def parseDecInt? (s : String) : Option Int :=
  let (neg, cs) := match s.toList with
    | '-' :: r => (true, r) | '+' :: r => (false, r) | r => (false, r)
  if cs.isEmpty || !cs.all Char.isDigit then none else
  let m := cs.foldl (fun acc d => acc * 10 + (d.toNat - '0'.toNat)) 0
  some (if neg then -(m : Int) else m)

/-- Number of significant bits of `n` (`0` for `0`). -/
@[expose] def bitLen (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

/-- The bit pattern of a float literal (`parse_float`). -/
@[expose] def parse? (s : String) (w t : Nat) : Option Nat := do
  let (sign, s2) :=
    if s.startsWith "-" then (2 ^ (t + w), (s.drop 1).toString)
    else if s.startsWith "+" then (0, (s.drop 1).toString)
    else (0, s)
  let maxE := (2 ^ w - 1) * 2 ^ t
  let quiet := 2 ^ (t - 1)
  if !s2.startsWith "0x" then
    if s2 == "0.0" then return sign
    if s2 == "Inf" then return sign + maxE
    if s2 == "NaN" then return sign + maxE + quiet
    if s2.startsWith "NaN:0x" then
      let p ← parseHexNat? (s2.drop 6).toString
      if p < quiet then return sign + maxE + quiet + p else none
    if s2.startsWith "sNaN:0x" then
      let p ← parseHexNat? (s2.drop 7).toString
      if 0 < p ∧ p < quiet then return sign + maxE + p else none
    none
  else
    let body := (s2.drop 2).toString
    let (mant, expStr) := match body.splitOn "p" with
      | [m] => (m, none)
      | [m, e] => (m, some e)
      | _ => ("", none)
    let exp0 : Int ← match expStr with
      | none => some 0
      | some e => parseDecInt? e
    let (intPart, fracPart) ← match mant.splitOn "." with
      | [i] => some (i, "")
      | [i, f] => some (i, f)
      | _ => none
    let digits := intPart ++ fracPart
    if digits.isEmpty || digits.length > 32 then none
    let sig ← parseHexNat? digits
    if sig = 0 then return sign
    let exp1 : Int := exp0 - 4 * fracPart.length
    let sb := bitLen sig
    -- normalise to `t + 1` significant bits
    let (sig, exp2) ←
      if sb > t + 1 then
        let adj := sb - (t + 1)
        if sig % 2 ^ adj ≠ 0 then none else some (sig / 2 ^ adj, exp1 + adj)
      else some (sig * 2 ^ (t + 1 - sb), exp1 - (t + 1 - sb : Nat))
    let tBits := sig % 2 ^ t
    let bias : Int := 2 ^ (w - 1) - 1
    let e : Int := exp2 + bias + t
    if e > 2 ^ w - 2 then none
    else if e > 0 then return sign + e.toNat * 2 ^ t + tBits
    else if 1 - e ≤ t then
      let adj := (1 - e).toNat
      if sig % 2 ^ adj ≠ 0 then none else return sign + sig / 2 ^ adj
    else none

/-- Lower-case hexadecimal digits of `n`, left-padded with zeros to `k` digits. -/
@[expose] def hexPad (n k : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (k - s.length) '0') ++ s

/-- Lower-case hexadecimal digits of `n` (no padding). -/
@[expose] def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- The text of a float bit pattern (`format_float`). -/
@[expose] def format (bits w t : Nat) : String :=
  let maxE := 2 ^ w - 1
  let tBits := bits % 2 ^ t
  let eBits := (bits / 2 ^ t) % 2 ^ w
  let signBit := (bits / 2 ^ (w + t)) % 2
  let bias : Int := 2 ^ (w - 1) - 1
  let e : Int := eBits - bias
  let emin : Int := 1 - bias
  let digits := (t + 3) / 4
  let leftT := tBits * 2 ^ (4 * digits - t)
  let pre := if signBit ≠ 0 then "-" else ""
  if eBits = 0 then
    if tBits = 0 then pre ++ "0.0"
    else pre ++ s!"0x0.{hexPad leftT digits}p{emin}"
  else if eBits = maxE then
    let pre := if signBit = 0 then "+" else pre
    if tBits = 0 then pre ++ "Inf"
    else
      let payload := tBits % 2 ^ (t - 1)
      if tBits / 2 ^ (t - 1) % 2 ≠ 0 then
        if payload ≠ 0 then pre ++ s!"NaN:0x{hex payload}" else pre ++ "NaN"
      else pre ++ s!"sNaN:0x{hex payload}"
  else pre ++ s!"0x1.{hexPad leftT digits}p{e}"

/-- Exponent and trailing-significand widths of a float type width (32 → binary32,
64 → binary64). -/
@[expose] def fields (width : Nat) : Nat × Nat := if width = 32 then (8, 23) else (11, 52)

end Clif.FloatLit
