/-
Handwritten executable, bit-exact models of the `libm` 0.2.16 functions reached through
`libm::Libm<f32>` / `libm::Libm<f64>` (Cranelift's constant folding of `sqrt`, `ceil`, `floor`,
`trunc`, `nearest` in `cranelift_codegen::ir::immediates`), as compiled natively on x86_64
(SSE2, `arch` implementations enabled):

- `sqrt`/`sqrtf`: `libm/src/math/arch/x86.rs`, the `sqrtsd`/`sqrtss` instruction: the correctly
  rounded (round-to-nearest-even) square root; a NaN input is returned quieted (sign and payload
  kept); a negative non-zero input (incl. `-inf`) gives the x86 default NaN (sign set, quiet bit
  only: `0xFFC00000` / `0xFFF8000000000000`); `±0` and `+inf` are returned unchanged.
- `ceil`/`floor`/`trunc`: `libm/src/math/generic/{ceil,floor,trunc}.rs`, transcribed on the bit
  patterns (NaNs are returned unchanged, payload and signalling bit included).
- `roundeven`: `libm/src/math/generic/rint.rs` `rint_round(x, Nearest)`: `x` itself when the
  biased exponent is `>= EXP_BIAS + SIG_BITS` (no fractional part, inf, NaN); otherwise
  `(x + 2^SIG_BITS) - 2^SIG_BITS` (resp. `(x - 2^SIG_BITS) + 2^SIG_BITS` for negative `x`) in
  round-to-nearest-even, which is exactly the integer nearest to `x` with ties to even; a zero
  result takes the sign of `x`. The model computes that integer exactly.

The functions work on the IEEE-754 bit patterns as natural numbers, parameterized by the format
(`SIG_BITS`, `EXP_BITS`), directly on the stored bits of the Aeneas library's `F32`/`F64`.

Note: these items are not in the latest templates (the e-graph mid-end that folds float constants
is still opaque); they are named as in the earlier full extraction's templates.
-/
module
public import Aeneas
public import ClifvGen.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace ClifvModels.Libm

/-- An IEEE-754 binary format: `sig` = `SIG_BITS` (stored significand bits), `exp` = `EXP_BITS`. -/
structure Fmt where
  sig : Nat
  exp : Nat

def f32 : Fmt := ⟨23, 8⟩
def f64 : Fmt := ⟨52, 11⟩

namespace Fmt
variable (F : Fmt)
def bits : Nat := 1 + F.exp + F.sig
def bias : Nat := 2 ^ (F.exp - 1) - 1
def expSat : Nat := 2 ^ F.exp - 1
def sigMask : Nat := 2 ^ F.sig - 1
def signMask : Nat := 2 ^ (F.exp + F.sig)
def allMask : Nat := 2 ^ F.bits - 1
/-- The quiet bit (most significant stored significand bit). -/
def quiet : Nat := 2 ^ (F.sig - 1)
end Fmt

/-- Biased exponent field. -/
def ex (F : Fmt) (x : Nat) : Nat := (x >>> F.sig) &&& F.expSat

def negative (F : Fmt) (x : Nat) : Bool := x &&& F.signMask != 0

/-- `generic::ceil`. -/
def ceil (F : Fmt) (x : Nat) : Nat :=
  let e : Int := (ex F x : Int) - F.bias
  if e ≥ F.sig then x
  else if e ≥ 0 then
    let m := F.sigMask >>> e.toNat
    if x &&& m == 0 then x
    else
      let ix := if negative F x then x else x + m
      ix &&& (F.allMask ^^^ m)
  else if negative F x then F.signMask
  else if x &&& (F.allMask >>> 1) != 0 then F.bias <<< F.sig
  else x

/-- `generic::floor`. -/
def floor (F : Fmt) (x : Nat) : Nat :=
  let e : Int := (ex F x : Int) - F.bias
  if e ≥ F.sig then x
  else if e ≥ 0 then
    let m := F.sigMask >>> e.toNat
    if x &&& m == 0 then x
    else
      let ix := if negative F x then x + m else x
      ix &&& (F.allMask ^^^ m)
  else if !negative F x then 0
  else if x &&& (F.allMask >>> 1) != 0 then F.signMask ||| (F.bias <<< F.sig)
  else x

/-- `generic::trunc`. -/
def trunc (F : Fmt) (x : Nat) : Nat :=
  let e : Int := (ex F x : Int) - F.bias
  if e ≥ F.sig then x
  else
    let mask := if e < 0 then F.signMask else F.allMask ^^^ (F.sigMask >>> e.toNat)
    if x &&& (F.allMask ^^^ mask) == 0 then x
    else x &&& mask

/-- The bit pattern of the (exactly representable) integer `0 < q ≤ 2^(sig+1)`, with sign `s`. -/
def ofInt (F : Fmt) (s : Nat) (q : Nat) : Nat :=
  let n := Nat.log2 q
  s ||| ((n + F.bias) <<< F.sig) ||| ((q <<< (F.sig - n)) &&& F.sigMask)

/-- `roundeven` (`rint_round(x, Nearest)`). -/
def roundeven (F : Fmt) (x : Nat) : Nat :=
  let E := ex F x
  if E ≥ F.bias + F.sig then x
  else
    let s := x &&& F.signMask
    let frac := x &&& F.sigMask
    -- |x| = m * 2^-(sh): for a normal `m = 2^sig + frac`, exponent `E`; subnormal: `E = 1`.
    let (m, Ee) := if E = 0 then (frac, 1) else (frac + 2 ^ F.sig, E)
    let sh := F.bias + F.sig - Ee
    let q := m >>> sh
    let r := m &&& (2 ^ sh - 1)
    let half := 2 ^ (sh - 1)
    let q := if r > half ∨ (r = half ∧ q % 2 = 1) then q + 1 else q
    if q = 0 then s else ofInt F s q

/-- `sqrtss`/`sqrtsd`. -/
def sqrt (F : Fmt) (x : Nat) : Nat :=
  let E := ex F x
  let frac := x &&& F.sigMask
  if E = F.expSat ∧ frac ≠ 0 then x ||| F.quiet                  -- NaN: quieted
  else if x &&& (F.allMask >>> 1) = 0 then x                      -- ±0
  else if negative F x then F.signMask ||| (F.expSat <<< F.sig) ||| F.quiet  -- default NaN
  else if E = F.expSat then x                                     -- +inf
  else
    -- x = m * 2^e
    let (m, e) : Nat × Int :=
      if E = 0 then (frac, 1 - (F.bias : Int) - F.sig)
      else (frac + 2 ^ F.sig, (E : Int) - F.bias - F.sig)
    let (m, e) := if e % 2 = 0 then (m, e) else (2 * m, e - 1)
    let k := F.sig + 2
    let M := m * 4 ^ k
    let r := Nat.sqrt M
    let sticky := r * r ≠ M
    let p := F.sig + 1
    let nb := Nat.log2 r + 1
    let d := nb - p
    let q := r >>> d
    let rem := r &&& (2 ^ d - 1)
    let half := 2 ^ (d - 1)
    let q := if rem > half ∨ (rem = half ∧ (sticky ∨ q % 2 = 1)) then q + 1 else q
    -- sqrt(x) ≈ q * 2^(d + e/2 - k); unbiased exponent of the result:
    let (q, d) := if q = 2 ^ p then (q / 2, d + 1) else (q, d)
    let ue : Int := (p - 1 : Nat) + (d : Int) + e / 2 - k
    (((ue + F.bias).toNat) <<< F.sig) ||| (q &&& F.sigMask)

def on32 (f : Fmt → Nat → Nat) (x : F32) : F32 :=
  F32.ofBitsNat (f f32 x.bitsNat)

def on64 (f : Fmt → Nat → Nat) (x : F64) : F64 :=
  F64.ofBitsNat (f f64 x.bitsNat)

end ClifvModels.Libm

open ClifvModels.Libm

/-- [libm::libm_helper::{libm::libm_helper::Libm<f32>}::sqrt]: `sqrtf` (`sqrtss`). -/
def libm.libm_helper.LibmF32.sqrt : F32 → Result F32 := fun x => ok (on32 ClifvModels.Libm.sqrt x)
/-- [libm::libm_helper::{libm::libm_helper::Libm<f32>}::ceil]: `ceilf`. -/
def libm.libm_helper.LibmF32.ceil : F32 → Result F32 := fun x => ok (on32 ClifvModels.Libm.ceil x)
/-- [libm::libm_helper::{libm::libm_helper::Libm<f32>}::floor]: `floorf`. -/
def libm.libm_helper.LibmF32.floor : F32 → Result F32 := fun x => ok (on32 ClifvModels.Libm.floor x)
/-- [libm::libm_helper::{libm::libm_helper::Libm<f32>}::trunc]: `truncf`. -/
def libm.libm_helper.LibmF32.trunc : F32 → Result F32 := fun x => ok (on32 ClifvModels.Libm.trunc x)
/-- [libm::libm_helper::{libm::libm_helper::Libm<f32>}::roundeven]: `roundevenf`. -/
def libm.libm_helper.LibmF32.roundeven : F32 → Result F32 :=
  fun x => ok (on32 ClifvModels.Libm.roundeven x)
/-- [libm::libm_helper::{libm::libm_helper::Libm<f64>}::sqrt]: `sqrt` (`sqrtsd`). -/
def libm.libm_helper.LibmF64.sqrt : F64 → Result F64 := fun x => ok (on64 ClifvModels.Libm.sqrt x)
/-- [libm::libm_helper::{libm::libm_helper::Libm<f64>}::ceil]: `ceil`. -/
def libm.libm_helper.LibmF64.ceil : F64 → Result F64 := fun x => ok (on64 ClifvModels.Libm.ceil x)
/-- [libm::libm_helper::{libm::libm_helper::Libm<f64>}::floor]: `floor`. -/
def libm.libm_helper.LibmF64.floor : F64 → Result F64 := fun x => ok (on64 ClifvModels.Libm.floor x)
/-- [libm::libm_helper::{libm::libm_helper::Libm<f64>}::trunc]: `trunc`. -/
def libm.libm_helper.LibmF64.trunc : F64 → Result F64 := fun x => ok (on64 ClifvModels.Libm.trunc x)
/-- [libm::libm_helper::{libm::libm_helper::Libm<f64>}::roundeven]: `roundeven`. -/
def libm.libm_helper.LibmF64.roundeven : F64 → Result F64 :=
  fun x => ok (on64 ClifvModels.Libm.roundeven x)
