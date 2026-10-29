module

public import FV.Float

@[expose] public section

/-!
`float-difftest [--seed N] [--count N] [--rne-only]`: generates differential test cases for the
shared IEEE core (`FV/Float`) and prints one line per case,

  `<class> <mode> <a> <b> <c> <result>`   (hexadecimal operands and the `IEEE` result)

for the host oracle `rust/crates/float-oracle` (`scripts/float-difftest.sh`), which recomputes
each case with Rust's `f32`/`f64` operations and compares. `count` cases per class; operands are
edge-biased (signed zeros, smallest/largest subnormals and normals, ±∞, quiet and signalling
NaNs with payloads, values near 1, integers and half-integers, values near the integer
saturation bounds, operand pairs that cancel or produce rounding ties). Modes: `n` (rne),
`p` (rpi), `m` (rmi), `z` (rz), `a` (rna). Arithmetic and format conversion cycle through the
four `FPCR` modes unless `--rne-only`; `rint`/`tofix` cycle through all five; `fromfix` is rne.
-/

open IEEE

namespace FloatDiff

abbrev GM := StateM StdGen

def rand (n : Nat) : GM Nat := do
  if n ≤ 1 then return 0
  let g ← get
  let (k, g') := randNat g 0 (n - 1)
  set g'
  return k

/-- A random `k`-bit number (`randNat` covers ranges well beyond 64 bits only coarsely). -/
def randBits (k : Nat) : GM Nat := do
  let mut r := 0
  for _ in [0:(k + 29) / 30] do
    r := r * 2 ^ 30 + (← rand (2 ^ 30))
  return r % 2 ^ k

/-- A fraction field: uniform, sparse (only the top `j` bits random, which produces ties and
exact results), all ones or zero. -/
def randFrac (f : Fmt) : GM Nat := do
  match ← rand 6 with
  | 0 | 1 => randBits f.F
  | 2 | 3 =>
    let j ← rand (f.F + 1)
    return (← randBits j) * 2 ^ (f.F - j)
  | 4 => return 2 ^ f.F - 1
  | _ => return 0

/-- An edge-biased encoding (as a `Nat`). -/
def special (f : Fmt) : GM Nat := do
  let sgn := if (← rand 2) = 0 then 0 else 2 ^ (f.E + f.F)
  let ones := f.expOnes
  let mag ← match ← rand 18 with
    | 0 => pure 0
    | 1 => pure 1
    | 2 => pure (2 ^ f.F - 1)
    | 3 => pure (2 ^ f.F)
    | 4 => pure ((ones - 1) * 2 ^ f.F + 2 ^ f.F - 1)
    | 5 => pure (ones * 2 ^ f.F)
    | 6 => return ones * 2 ^ f.F + 2 ^ (f.F - 1) + (← randBits (f.F - 1))
    | 7 => return ones * 2 ^ f.F + 1 + (← randBits (f.F - 1)) % (2 ^ (f.F - 1) - 1)
    | 8 => randFrac f
    | 9 | 10 => return (f.bias + (← rand 7) - 3) * 2 ^ f.F + (← randFrac f)
    | 11 | 12 =>
      -- integers and few-fraction-bit values (rounding ties of `rint`/`tofix`)
      let e := f.bias + (← rand (f.F + 3))
      let keep ← rand 4
      let fr ← randBits f.F
      return e * 2 ^ f.F + fr / 2 ^ (f.F - Nat.min f.F (e - f.bias + keep)) *
        2 ^ (f.F - Nat.min f.F (e - f.bias + keep))
    | 13 =>
      -- near the integer saturation bounds 2^31, 2^32, 2^63, 2^64
      let k := #[31, 32, 63, 64][← rand 4]!
      let e := f.bias + k - 1 + (← rand 3)
      let fr ← match ← rand 3 with
        | 0 => pure 0
        | 1 => pure (2 ^ f.F - 1)
        | _ => randBits f.F
      return Nat.min e (ones - 1) * 2 ^ f.F + fr
    | 14 | 15 => return (1 + (← rand (ones - 1))) * 2 ^ f.F + (← randFrac f)
    | _ => randBits (f.E + f.F)
  return sgn + mag

/-- A second operand related to `a`: its negation (cancellation), a few ulps away, or a smaller
exponent with a sparse fraction (alignment, ties and sticky bits in sums). -/
def related (f : Fmt) (a : Nat) : GM Nat := do
  let top := 2 ^ (f.E + f.F)
  match ← rand 4 with
  | 0 => return (a + top) % (2 * top)
  | 1 => return (a + (← rand 7) - 3) % (2 * top)
  | _ =>
    let e := a / 2 ^ f.F % 2 ^ f.E
    let e' := e - Nat.min e (← rand (f.F + 5))
    let sgn := if (← rand 2) = 0 then 0 else top
    return sgn + e' * 2 ^ f.F + (← randFrac f)

def operand2 (f : Fmt) (a : Nat) : GM Nat := do
  if (← rand 3) = 0 then related f a else special f

def bv (f : Fmt) (n : Nat) : Bits f := BitVec.ofNat _ n

/-- A binary64 near the binary32 range: rounding position at fraction bit 29 (ties and sticky
bits), exponents across the binary32 subnormal/normal/overflow boundaries. -/
def nearB32 : GM Nat := do
  let sgn := if (← rand 2) = 0 then 0 else 2 ^ 63
  let e := 1023 - 155 + (← rand 290)
  let lo ← match ← rand 4 with
    | 0 => pure 0
    | 1 => pure (2 ^ 28)
    | 2 => return 2 ^ 28 + 1 + (← randBits 28)
    | _ => randBits 29
  return sgn + e * 2 ^ 52 + (← randBits 23) * 2 ^ 29 + lo

/-- An edge-biased `M`-bit integer operand. -/
def intOperand (M : Nat) : GM Nat := do
  match ← rand 8 with
  | 0 => return #[0, 1, 2 ^ M - 1, 2 ^ (M - 1), 2 ^ (M - 1) - 1, 2 ^ (M - 1) + 1][← rand 6]!
  | 1 | 2 =>
    -- `k` significant bits shifted: exact values, ties and sticky bits at the rounding position
    let k := 1 + (← rand 30)
    let sh ← rand M
    return ((← randBits k) * 2 ^ sh) % 2 ^ M
  | 3 =>
    let p ← rand M
    return (2 ^ p + (← rand 5) - 2) % 2 ^ M
  | 4 => return (2 ^ M - (← rand 1000)) % 2 ^ M
  | _ => randBits M

def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def modeChar : RMode → Char
  | .rne => 'n' | .rpi => 'p' | .rmi => 'm' | .rz => 'z' | .rna => 'a'

def fpcrModes : Array RMode := #[.rne, .rpi, .rmi, .rz]
def allModes : Array RMode := #[.rne, .rpi, .rmi, .rz, .rna]

def line (cls : String) (rm : RMode) (a b c r : Nat) : String :=
  s!"{cls} {modeChar rm} {hex a} {hex b} {hex c} {hex r}\n"

def cmpCode : Cmp → Nat
  | .lt => 0 | .eq => 1 | .gt => 2 | .un => 3

/-- One case of class `cls`; `i` selects the rounding mode. -/
def genCase (cls : String) (i : Nat) (rneOnly : Bool) : GM String := do
  let fm := if rneOnly then RMode.rne else fpcrModes[i % 4]!
  let am := allModes[i % 5]!
  let fmtOf (s : String) : Fmt := if s = "32" then .b32 else .b64
  match cls.splitOn "." with
  | [op, w] =>
    let f := fmtOf w
    let a ← special f
    match op with
    | "add" | "sub" | "mul" | "div" =>
      let b ← operand2 f a
      let r : Bits f := match op with
        | "add" => add f fm (bv f a) (bv f b)
        | "sub" => sub f fm (bv f a) (bv f b)
        | "mul" => mul f fm (bv f a) (bv f b)
        | _ => div f fm (bv f a) (bv f b)
      return line cls fm a b 0 r.toNat
    | "sqrt" => return line cls fm a 0 0 (sqrt f fm (bv f a)).toNat
    | "fma" =>
      -- `mulAdd addend a b`; the addend sometimes cancels the rounded product
      let b ← operand2 f a
      let c ← match ← rand 3 with
        | 0 => pure (neg f (mul f .rne (bv f a) (bv f b))).toNat
        | 1 => related f a
        | _ => special f
      return line cls fm a b c (mulAdd f fm (bv f c) (bv f a) (bv f b)).toNat
    | "cmp" =>
      let b ← if (← rand 4) = 0 then pure a else operand2 f a
      return line cls .rne a b 0 (cmpCode (compare f (bv f a) (bv f b)))
    | "rint" => return line cls am a 0 0 (roundInt f am (bv f a)).toNat
    | _ => return ""
  | ["cvt", "64", "32"] =>
    let a ← if (← rand 2) = 0 then nearB32 else special .b64
    return line cls fm a 0 0 (convert .b64 .b32 fm (bv .b64 a)).toNat
  | ["cvt", "32", "64"] =>
    let a ← special .b32
    return line cls fm a 0 0 (convert .b32 .b64 fm (bv .b32 a)).toNat
  | ["tofix", w, it] =>
    let f := fmtOf w
    let a ← special f
    let unsigned := it.startsWith "u"
    let M := (it.drop 1).toNat!
    return line cls am a 0 0 (toFixed f (bv f a) unsigned M am).toNat
  | ["fromfix", it, w] =>
    let f := fmtOf w
    let unsigned := it.startsWith "u"
    let M := (it.drop 1).toNat!
    let x ← intOperand M
    return line cls .rne x 0 0 (fromFixed f M (BitVec.ofNat M x) unsigned .rne).toNat
  | _ => return ""

def classes : List String :=
  (["add", "sub", "mul", "div", "sqrt", "fma", "cmp", "rint"].flatMap fun op =>
      [s!"{op}.32", s!"{op}.64"]) ++
  ["cvt.64.32", "cvt.32.64"] ++
  (["32", "64"].flatMap fun w => ["i32", "u32", "i64", "u64"].map fun it => s!"tofix.{w}.{it}") ++
  (["i32", "u32", "i64", "u64"].flatMap fun it => ["32", "64"].map fun w => s!"fromfix.{it}.{w}")

structure Opts where
  seed : Nat := 1
  count : Nat := 100000
  rneOnly : Bool := false
  only : Option String := none

partial def parseArgs : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--seed" :: n :: r, o => parseArgs r { o with seed := n.toNat! }
  | "--count" :: n :: r, o => parseArgs r { o with count := n.toNat! }
  | "--rne-only" :: r, o => parseArgs r { o with rneOnly := true }
  | "--only" :: s :: r, o => parseArgs r { o with only := some s }
  | a :: _, _ => .error s!"unknown argument {a}"

end FloatDiff

open FloatDiff in
def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error e =>
    IO.eprintln e
    return 2
  | .ok o =>
    let out ← IO.getStdout
    let mut g := mkStdGen o.seed
    for cls in classes do
      if let some s := o.only then
        unless (cls.splitOn s).length > 1 do continue
      let mut buf := ""
      for i in [0:o.count] do
        let (l, g') := (genCase cls i o.rneOnly).run g
        g := g'
        buf := buf ++ l
        if i % 4096 = 4095 then
          out.putStr buf
          buf := ""
      out.putStr buf
    out.flush
    return 0
