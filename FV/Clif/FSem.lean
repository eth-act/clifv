module

public import FV.Clif.Syntax
public import FV.Float

@[expose] public section

/-!
# CLIF float semantics (`Clif.FSem`)

The float operations of `Inst.float` on IEEE 754 bit patterns, defined by the AArch64 ASL
functions of `FV/Float` (namespace `IEEE`) with the Linux default `FPCR = 0` and rounding to
nearest, ties to even (`docs/plans/floats.md`, "Semantics decisions"; `docs/contracts/float.md`):

* arithmetic NaN results are those of `FPProcessNaNs` with `FPCR.DN = 0` (the first signalling
  NaN operand quietened, else the first quiet NaN operand, else the default NaN). Cranelift
  (`docs/ir.md`, "Floating point types") leaves the sign and, unless every NaN input is
  canonical, the payload nondeterministic; this is one admissible choice, the target's;
* `fmin`/`fmax` are `FPMin`/`FPMax` (NaN-propagating, `-0 < +0`, Cranelift's WebAssembly rules);
* `fneg`/`fabs`/`fcopysign` change the sign bit only;
* `ceil`/`floor`/`trunc`/`nearest` are `FPRoundInt` toward +∞/−∞/zero/nearest-even;
* `fcvt_to_{u,s}int` trap `bad_toint` on NaN and `int_ovf` when the truncated value does not fit;
  the `_sat` forms saturate and map NaN to 0 (`FPToFixed`, round toward zero);
* `fcvt_from_{u,s}int`, `fdemote` round to nearest even (`FixedToFP`, `FPConvert`);
  `fpromote` is exact (`FPConvert`; a signalling NaN is quietened).
-/

namespace Clif.FSem

open IEEE (Fmt Cmp RMode)

/-- The IEEE format of a float type. -/
def fmt? : Ty → Option Fmt
  | .f32 => some Fmt.b32
  | .f64 => some Fmt.b64
  | _ => none

/-- A binary operation on the bits of a float type (`none` at other types). -/
def lift2 (g : (f : Fmt) → IEEE.Bits f → IEEE.Bits f → IEEE.Bits f) :
    (ty : Ty) → BitVec ty.width → BitVec ty.width → Option (BitVec ty.width)
  | .f32, a, b => some (g Fmt.b32 a b)
  | .f64, a, b => some (g Fmt.b64 a b)
  | _, _, _ => none

/-- A unary operation on the bits of a float type. -/
def lift1 (g : (f : Fmt) → IEEE.Bits f → IEEE.Bits f) :
    (ty : Ty) → BitVec ty.width → Option (BitVec ty.width)
  | .f32, a => some (g Fmt.b32 a)
  | .f64, a => some (g Fmt.b64 a)
  | _, _ => none

/-- A ternary operation on the bits of a float type. -/
def lift3 (g : (f : Fmt) → IEEE.Bits f → IEEE.Bits f → IEEE.Bits f → IEEE.Bits f) :
    (ty : Ty) → BitVec ty.width → BitVec ty.width → BitVec ty.width → Option (BitVec ty.width)
  | .f32, a, b, c => some (g Fmt.b32 a b c)
  | .f64, a, b, c => some (g Fmt.b64 a b c)
  | _, _, _, _ => none

/-- `fcopysign x y`: `x` with the sign bit of `y`. -/
def copysign (f : Fmt) (x y : IEEE.Bits f) : IEEE.Bits f :=
  let s : IEEE.Bits f := BitVec.ofNat _ (2 ^ (f.E + f.F))
  (x &&& ~~~s) ||| (y &&& s)

/-- Binary operations (`fadd fsub fmul fdiv fmin fmax fcopysign`). -/
def binary : FOp → Option ((f : Fmt) → IEEE.Bits f → IEEE.Bits f → IEEE.Bits f)
  | .fadd => some fun f => IEEE.add f .rne
  | .fsub => some fun f => IEEE.sub f .rne
  | .fmul => some fun f => IEEE.mul f .rne
  | .fdiv => some fun f => IEEE.div f .rne
  | .fmin => some fun f => IEEE.min f .rne
  | .fmax => some fun f => IEEE.max f .rne
  | .fcopysign => some copysign
  | _ => none

/-- Unary same-type operations (`fneg fabs sqrt ceil floor trunc nearest`). -/
def unary : FOp → Option ((f : Fmt) → IEEE.Bits f → IEEE.Bits f)
  | .fneg => some IEEE.neg
  | .fabs => some IEEE.abs
  | .sqrt => some fun f => IEEE.sqrt f .rne
  | .ceil => some fun f => IEEE.roundInt f .rpi
  | .floor => some fun f => IEEE.roundInt f .rmi
  | .trunc => some fun f => IEEE.roundInt f .rz
  | .nearest => some fun f => IEEE.roundInt f .rne
  | _ => none

/-- `fma x y z = x * y + z`, rounded once (`FPMulAdd(z, x, y)`). -/
def fma (f : Fmt) (x y z : IEEE.Bits f) : IEEE.Bits f := IEEE.mulAdd f .rne z x y

/-- `fcmp cc` on the comparison result (`FloatCC`, `docs/ir.md` table). -/
def condHolds : FloatCC → Cmp → Bool
  | .eq, c => c == .eq
  | .ne, c => c != .eq
  | .lt, c => c == .lt
  | .le, c => c == .lt || c == .eq
  | .gt, c => c == .gt
  | .ge, c => c == .gt || c == .eq
  | .ord, c => c != .un
  | .uno, c => c == .un
  | .one, c => c == .lt || c == .gt
  | .ueq, c => c == .un || c == .eq
  | .ult, c => c == .un || c == .lt
  | .ule, c => c == .un || c == .lt || c == .eq
  | .ugt, c => c == .un || c == .gt
  | .uge, c => c == .un || c == .gt || c == .eq

/-- `fcmp cc x y` at a float type. -/
def fcmp (cc : FloatCC) : (ty : Ty) → BitVec ty.width → BitVec ty.width → Option Bool
  | .f32, a, b => some (condHolds cc (IEEE.compare Fmt.b32 a b))
  | .f64, a, b => some (condHolds cc (IEEE.compare Fmt.b64 a b))
  | _, _, _ => none

/-- `fpromote.f64 x` (`x : f32`). -/
def fpromote (x : BitVec 32) : BitVec 64 := IEEE.convert Fmt.b32 Fmt.b64 .rne x

/-- `fdemote.f32 x` (`x : f64`). -/
def fdemote (x : BitVec 64) : BitVec 32 := IEEE.convert Fmt.b64 Fmt.b32 .rne x

/-- The truncation of a float to an integer of width `w` (`unsigned` or signed), saturating,
NaN ↦ 0 (`fcvt_to_{u,s}int_sat`). -/
def toIntSat (unsigned : Bool) (w : Nat) : (ty : Ty) → BitVec ty.width → Option (BitVec w)
  | .f32, a => some (IEEE.toFixed Fmt.b32 a unsigned w .rz)
  | .f64, a => some (IEEE.toFixed Fmt.b64 a unsigned w .rz)
  | _, _ => none

/-- The trapping truncation (`fcvt_to_{u,s}int`): `bad_toint` on NaN, `int_ovf` if the
truncated value is outside the range of the `w`-bit result. -/
def toInt (unsigned : Bool) (w : Nat) : (ty : Ty) → BitVec ty.width → Option (Except TrapCode (BitVec w))
  | .f32, a => some (check (IEEE.isNaN Fmt.b32 a) (IEEE.truncInt? Fmt.b32 a))
  | .f64, a => some (check (IEEE.isNaN Fmt.b64 a) (IEEE.truncInt? Fmt.b64 a))
  | _, _ => none
where
  check (nan : Bool) (t : Option Int) : Except TrapCode (BitVec w) :=
    if nan then .error .badToint else
    match t with
    | none => .error .intOvf
    | some i =>
      let lo : Int := if unsigned then 0 else -(2 ^ (w - 1) : Nat)
      let hi : Int := if unsigned then (2 ^ w : Nat) - 1 else (2 ^ (w - 1) : Nat) - 1
      if lo ≤ i ∧ i ≤ hi then .ok (BitVec.ofInt w i) else .error .intOvf

/-- `fcvt_from_{u,s}int.ty x` for an integer `x` of width `w`. -/
def fromInt (unsigned : Bool) {w : Nat} (x : BitVec w) : (ty : Ty) → Option (BitVec ty.width)
  | .f32 => some (IEEE.fromFixed Fmt.b32 w x unsigned .rne)
  | .f64 => some (IEEE.fromFixed Fmt.b64 w x unsigned .rne)
  | _ => none

end Clif.FSem
