/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license.
-/
import FV.Clif.Sem
import FV.Clif.FSem

/-!
# CLIF vector semantics (`Clif.VSem`, S12d, #36)

The meaning of `Inst.vector op ty args imm` (`VecOp`) on the bits of its operands, used by
`Clif.run` (`evalInst`). A vector of shape `s` is its raw bits (`BitVec s.width`); lane `i` is
`Vec.lane s.laneBits x i` (lane 0 least significant, `docs/plans/simd.md` §2). The lane-wise
operations apply the scalar semantics at the lane type (`Clif.Sem`, `Clif.FSem`), lane by lane;
the vector-only opcodes follow Cranelift's interpreter (`interpreter/src/step.rs`, 0.136.1):

* integer lanes wrap; a shift amount is a scalar, taken modulo the lane width (`shift_amt`);
* `icmp`/`fcmp` give all-ones (true) or zero lanes of the integer shape;
* `avg_round` is the unsigned rounding average `(x + y + 1) >> 1` without overflow (Arm's
  `urhadd`);
* `sqmul_round_sat` is `(x·y + 2^(n-2)) >> (n-1)` saturated to the signed lane range;
* `snarrow`/`unarrow`/`uunarrow` clamp the lanes of `x` then `y` (signed to signed, signed to
  unsigned, unsigned to unsigned bounds) and truncate them to half width;
* `iadd_pairwise x y`: lane `i` is the sum of lanes `2i` and `2i+1` of the concatenation of the
  lanes of `x` and `y`;
* `shuffle x y mask`: byte `i` is byte `mask[i]` of the 32 bytes of `x` then `y` (0 if
  `mask[i] ≥ 32`); `swizzle x y`: byte `i` is byte `y[i]` of `x` (0 if `y[i] ≥ 16`);
* `vhigh_bits.ty x`: bit `i` is the top bit of lane `i`, truncated to `ty`;
* `fvdemote` rounds the two `f64` lanes to `f32` and zeroes lanes 2 and 3; `fvpromote_low`
  converts lanes 0 and 1 of an `f32x4` exactly.

`none` means the operands do not fit the operation (wrong types or arity, an out-of-range
lane index, an integer operation on float lanes): `Clif.run` is `stuck` there, as for an
ill-typed scalar instruction.
-/

namespace Clif.VSem

/-- Lane `i` of a vector of shape `s`, at the lane type. -/
def lane (s : VShape) (x : BitVec s.width) (i : Nat) : BitVec s.laneTy.width :=
  (Vec.lane s.laneBits x i).cast s.laneTy_width.symm

/-- The vector of shape `s` whose lane `i` is `f i`. -/
def mk (s : VShape) (f : Nat → BitVec s.laneTy.width) : BitVec s.width :=
  Vec.ofLanes s.laneBits (fun i => (f i).cast s.laneTy_width) s.lanes

theorem lane_mk (s : VShape) (f : Nat → BitVec s.laneTy.width) {i : Nat} (hi : i < s.lanes) :
    lane s (mk s f) i = f i := by
  simp only [lane, mk]
  rw [Vec.lane_ofLanes (w := s.width) _ _ (by simp [VShape.width]) hi]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_cast, BitVec.toNat_cast]

/-- All-ones or zero lane bits. -/
def mask (w : Nat) (b : Bool) : BitVec w := if b then BitVec.allOnes w else 0

/-- The vector value of shape `s` with lanes `f`. -/
def val (s : VShape) (f : Nat → BitVec s.laneTy.width) : Val := ⟨.vec s, mk s f⟩

/-- The bits of an operand of shape `s`. -/
def arg (s : VShape) (v : Val) : Option (BitVec s.width) := v.as? (.vec s)

/-- A lane-wise integer comparison or float comparison result at shape `s`'s integer shape. -/
def cmpVal (s : VShape) (p : Nat → Bool) : Val :=
  ⟨.vec s.intShape, mk s.intShape fun i => mask _ (p i)⟩

/-- Clamp the integer `i` to `[lo, hi]`. -/
def clamp (lo hi i : Int) : Int := max lo (min hi i)

/-- The narrowing of one lane (`snarrow`, `unarrow`, `uunarrow`) to `nb` bits: `x` read signed
(`snarrow`, `unarrow`) or unsigned (`uunarrow`), clamped to the signed (`snarrow`) or unsigned
`nb`-bit range. -/
def narrowLane (op : VecOp) (nb : Nat) {w : Nat} (x : BitVec w) : BitVec nb :=
  let v : Int := if op == .uunarrow then x.toNat else x.toInt
  let (lo, hi) : Int × Int :=
    if op == .snarrow then (-(2 ^ (nb - 1) : Nat), (2 ^ (nb - 1) : Nat) - 1)
    else (0, (2 ^ nb : Nat) - 1)
  BitVec.ofInt nb (clamp lo hi v)

/-- `sqmul_round_sat` on one lane of `n` bits. -/
def sqmulLane {n : Nat} (x y : BitVec n) : BitVec n :=
  let z : Int := (x.toInt * y.toInt + 2 ^ (n - 2)) >>> (n - 1)
  BitVec.ofInt n (clamp (-(2 ^ (n - 1) : Nat)) ((2 ^ (n - 1) : Nat) - 1) z)

/-- Byte `j` of the bits `x` (0 beyond the width). -/
def byteAt {w : Nat} (x : BitVec w) (j : Nat) : BitVec 8 := Vec.byte x j

/-- The value with bytes `f 0 … f 15` of shape `s` (a 128-bit shape). -/
def ofBytes (s : VShape) (f : Nat → BitVec 8) : Val :=
  ⟨.vec s, Vec.ofLanes 8 f 16⟩

/-- **The semantics of `Inst.vector op ty` on the operand values `vs`** (`none`: `stuck`). -/
def eval (op : VecOp) (ty : Ty) (vs : List Val) (imm : Nat) : Option Val := do
  match op with
  | .vhighBits =>
    let [a] := vs | none
    let .vec s := a.ty | none
    guard ty.isInt
    let x ← arg s a
    let n := (List.range s.lanes).foldl (fun acc i =>
      acc + (if (Vec.lane s.laneBits x i).msb then 2 ^ i else 0)) 0
    pure (Val.ofNat ty n)
  | _ =>
  let .vec s := ty | none
  let int := !s.isFloatLane
  match op, vs with
  | .unary u, [a] => do
    guard (int || u == .bnot)
    let x ← arg s a
    pure (val s fun i => Sem.unary u (lane s x i))
  | .binary b, [a, c] => do
    let x ← arg s a
    if b.isShift then
      guard (int && c.ty.isInt)
      pure (val s fun i => (Sem.shift b (lane s x i) c.bits).getD 0)
    else
      guard (int || b == .band || b == .bor || b == .bxor)
      let y ← arg s c
      pure (val s fun i => Sem.binary b (lane s x i) (lane s y i))
  | .icmp cc, [a, c] => do
    guard int
    let x ← arg s a
    let y ← arg s c
    pure (cmpVal s fun i => Sem.intcc cc (lane s x i) (lane s y i))
  | .bitselect, [m, a, c] => do
    let k ← arg s m
    let x ← arg s a
    let y ← arg s c
    pure ⟨.vec s, Sem.bitselect k x y⟩
  | .float (.fcmp cc), [a, c] => do
    guard (!int)
    let x ← arg s a
    let y ← arg s c
    let r ← (List.range s.lanes).mapM fun i => FSem.fcmp cc s.laneTy (lane s x i) (lane s y i)
    pure (cmpVal s fun i => r.getD i false)
  | .float .fma, [a, b, c] => do
    guard (!int)
    let x ← arg s a
    let y ← arg s b
    let z ← arg s c
    let r ← (List.range s.lanes).mapM fun i =>
      FSem.lift3 FSem.fma s.laneTy (lane s x i) (lane s y i) (lane s z i)
    pure (val s fun i => r.getD i 0)
  | .float f, [a] =>
    match f with
    | .fcvtToUintSat | .fcvtToSintSat => do
      -- `ty` is the integer result shape; the operand has the float shape of the same lanes
      guard int
      let .vec sa := a.ty | none
      guard (sa.isFloatLane && sa.intShape == s)
      let x ← arg sa a
      let r ← (List.range s.lanes).mapM fun i =>
        FSem.toIntSat (f == .fcvtToUintSat) s.laneBits sa.laneTy (lane sa x i)
      pure ⟨.vec s, Vec.ofLanes s.laneBits (fun i => r.getD i 0) s.lanes⟩
    | .fcvtFromUint | .fcvtFromSint => do
      -- `ty` is the float result shape; the operand has its integer shape
      guard (!int)
      let x ← arg s.intShape a
      let r ← (List.range s.lanes).mapM fun i =>
        FSem.fromInt (f == .fcvtFromUint) (Vec.lane s.laneBits x i) s.laneTy
      pure (val s fun i => r.getD i 0)
    | _ => do
      guard (!int)
      let g ← FSem.unary f
      let x ← arg s a
      let r ← (List.range s.lanes).mapM fun i => FSem.lift1 g s.laneTy (lane s x i)
      pure (val s fun i => r.getD i 0)
  | .float f, [a, c] => do
    guard (!int)
    let g ← FSem.binary f
    let x ← arg s a
    let y ← arg s c
    let r ← (List.range s.lanes).mapM fun i => FSem.lift2 g s.laneTy (lane s x i) (lane s y i)
    pure (val s fun i => r.getD i 0)
  | .splat, [a] => do
    let x ← a.as? s.laneTy
    pure (val s fun _ => x)
  | .scalarToVector, [a] => do
    let x ← a.as? s.laneTy
    pure (val s fun i => if i = 0 then x else 0)
  | .vconst, [] =>
    pure ⟨.vec s, BitVec.ofNat s.width imm⟩
  | .extractlane, [a] => do
    guard (imm < s.lanes)
    let x ← arg s a
    pure ⟨s.laneTy, lane s x imm⟩
  | .insertlane, [a, b] => do
    guard (imm < s.lanes)
    let x ← arg s a
    let y ← b.as? s.laneTy
    pure (val s fun i => if i = imm then y else lane s x i)
  | .shuffle, [a, b] => do
    guard (s.width == 128)
    let x ← arg s a
    let y ← arg s b
    pure (ofBytes s fun i =>
      let m := (Vec.byte (BitVec.ofNat 128 imm) i).toNat
      if m < 16 then byteAt x m else if m < 32 then byteAt y (m - 16) else 0)
  | .swizzle, [a, b] => do
    guard (s.width == 128)
    let x ← arg s a
    let y ← arg s b
    pure (ofBytes s fun i =>
      let m := (byteAt y i).toNat
      if m < 16 then byteAt x m else 0)
  | .swidenLow, [a] | .swidenHigh, [a] | .uwidenLow, [a] | .uwidenHigh, [a] => do
    let sw ← s.widen?
    let x ← arg s a
    let off := if op == .swidenHigh || op == .uwidenHigh then sw.lanes else 0
    let signed := op == .swidenLow || op == .swidenHigh
    pure ⟨.vec sw, Vec.ofLanes sw.laneBits (fun i =>
      let l := Vec.lane s.laneBits x (off + i)
      if signed then l.signExtend sw.laneBits else l.zeroExtend sw.laneBits) sw.lanes⟩
  | .snarrow, [a, b] | .unarrow, [a, b] | .uunarrow, [a, b] => do
    let sn ← s.narrow?
    let x ← arg s a
    let y ← arg s b
    pure ⟨.vec sn, Vec.ofLanes sn.laneBits (fun i =>
      if i < s.lanes then narrowLane op sn.laneBits (Vec.lane s.laneBits x i)
      else narrowLane op sn.laneBits (Vec.lane s.laneBits y (i - s.lanes))) sn.lanes⟩
  | .iaddPairwise, [a, b] => do
    guard int
    let x ← arg s a
    let y ← arg s b
    let h := s.lanes / 2
    let pair (v : BitVec s.width) (j : Nat) : BitVec s.laneTy.width :=
      lane s v (2 * j) + lane s v (2 * j + 1)
    pure (val s fun i => if i < h then pair x i else pair y (i - h))
  | .avgRound, [a, b] => do
    guard int
    let x ← arg s a
    let y ← arg s b
    pure (val s fun i =>
      BitVec.ofNat _ (((lane s x i).toNat + (lane s y i).toNat + 1) / 2))
  | .sqmulRoundSat, [a, b] => do
    guard int
    let x ← arg s a
    let y ← arg s b
    pure (val s fun i => sqmulLane (lane s x i) (lane s y i))
  | .vallTrue, [a] | .vanyTrue, [a] => do
    let x ← arg s a
    let nz := (List.range s.lanes).map fun i => Vec.lane s.laneBits x i != 0
    pure (Val.ofBool (if op == .vallTrue then nz.all id else nz.any id))
  | .fvdemote, [a] => do
    guard (s == .f64x2)
    let x ← arg s a
    pure ⟨.vec .f32x4, Vec.ofLanes 32 (fun i =>
      if i < 2 then FSem.fdemote (Vec.lane 64 x i) else 0) 4⟩
  | .fvpromoteLow, [a] => do
    guard (s == .f32x4)
    let x ← arg s a
    pure ⟨.vec .f64x2, Vec.ofLanes 64 (fun i => FSem.fpromote (Vec.lane 32 x i)) 2⟩
  | _, _ => none

end Clif.VSem
