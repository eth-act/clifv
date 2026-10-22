/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license.
-/

/-!
# CLIF vector values (S12b, #36)

The value-level semantics of CLIF's vector types (`docs/plans/simd.md` §2), independent of
`Clif.Ty`: S12d adds `Ty.vec (s : VShape)` and uses these functions in `Clif.run`.

* `VShape`: the legal 64- and 128-bit shapes (`i8x8 i16x4 i32x2 f32x2`,
  `i8x16 i16x8 i32x4 i64x2 f32x4 f64x2`), with `laneBits`, `lanes`, `width`, CLIF names.
* A vector value is its raw bits, `BitVec s.width`. Lane `i` is bits
  `[i·laneBits, (i+1)·laneBits)` (`lane`, an `extractLsb'`), lane 0 least significant: the order
  of Cranelift's interpreter (`interpreter/src/step.rs` `extractlanes`: lane `i` is bytes
  `[i·n, (i+1)·n)` of the 16-byte array, little-endian within the lane) and of the Arm model's
  `elem_get` (`FV/Arm/Insts/Common.lean`, the same `extractLsb'`).
* Memory: a vector is stored as its `width/8` bytes in little-endian order (`Mem.writeBits`
  with `big = false`), so lane `i`'s byte `j` is byte `i·laneBits/8 + j` of the value
  (`byte_lane`).
* `bitcast` with little-endian (or no) flags between equal widths is the identity on the bits
  (`bitcastLE`): every byte stays where it is (`byte_bitcastLE`).
-/

namespace Clif

/-- Shapes of the 64- and 128-bit CLIF vector types. -/
inductive VShape where
  | i8x8 | i16x4 | i32x2 | f32x2
  | i8x16 | i16x8 | i32x4 | i64x2 | f32x4 | f64x2
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace VShape

/-- Bits per lane. -/
def laneBits : VShape → Nat
  | i8x8 | i8x16 => 8
  | i16x4 | i16x8 => 16
  | i32x2 | f32x2 | i32x4 | f32x4 => 32
  | i64x2 | f64x2 => 64

/-- Number of lanes. -/
def lanes : VShape → Nat
  | i8x16 => 16
  | i8x8 | i16x8 => 8
  | i16x4 | i32x4 | f32x4 => 4
  | i32x2 | f32x2 | i64x2 | f64x2 => 2

/-- Bit width of the vector. -/
def width (s : VShape) : Nat := s.lanes * s.laneBits

/-- Float lanes (`f32x2`, `f32x4`, `f64x2`). -/
def isFloatLane : VShape → Bool
  | f32x2 | f32x4 | f64x2 => true
  | _ => false

/-- CLIF spelling. -/
def name : VShape → String
  | i8x8 => "i8x8" | i16x4 => "i16x4" | i32x2 => "i32x2" | f32x2 => "f32x2"
  | i8x16 => "i8x16" | i16x8 => "i16x8" | i32x4 => "i32x4" | i64x2 => "i64x2"
  | f32x4 => "f32x4" | f64x2 => "f64x2"

def all : List VShape := [i8x8, i16x4, i32x2, f32x2, i8x16, i16x8, i32x4, i64x2, f32x4, f64x2]

def ofName? (n : String) : Option VShape := all.find? (·.name == n)

theorem mem_all (s : VShape) : s ∈ all := by cases s <;> decide

theorem ofName?_name (s : VShape) : ofName? s.name = some s := by cases s <;> decide

theorem width_eq (s : VShape) : s.width = 64 ∨ s.width = 128 := by cases s <;> decide

theorem laneBits_pos (s : VShape) : 0 < s.laneBits := by cases s <;> decide

theorem laneBits_mod_eight (s : VShape) : s.laneBits % 8 = 0 := by cases s <;> decide

end VShape

namespace Vec

open BitVec

/-- Lane `i` of `x` with `lb`-bit lanes (lane 0 least significant). -/
def lane (lb : Nat) (x : BitVec w) (i : Nat) : BitVec lb := x.extractLsb' (i * lb) lb

/-- `x` with lane `i` replaced by `y`. -/
def setLane (lb : Nat) (x : BitVec w) (i : Nat) (y : BitVec lb) : BitVec w :=
  (x &&& ~~~((BitVec.allOnes lb).setWidth w <<< (i * lb))) ||| (y.setWidth w <<< (i * lb))

/-- Byte `j` (little-endian, byte 0 least significant). -/
def byte (x : BitVec w) (j : Nat) : BitVec 8 := lane 8 x j

/-- `bitcast` with little-endian (or no) flags between types of the same width. -/
def bitcastLE (h : w = w') (x : BitVec w) : BitVec w' := x.cast h

theorem getLsbD_lane (lb : Nat) (x : BitVec w) (i k : Nat) :
    (lane lb x i).getLsbD k = (decide (k < lb) && x.getLsbD (i * lb + k)) := by
  simp [lane, BitVec.getLsbD_extractLsb']

theorem getLsbD_setLane (lb : Nat) (x : BitVec w) (i : Nat) (y : BitVec lb) (k : Nat) :
    (setLane lb x i y).getLsbD k =
      if i * lb ≤ k ∧ k < i * lb + lb then (decide (k < w) && y.getLsbD (k - i * lb))
      else x.getLsbD k := by
  by_cases hk : k < w
  · simp only [setLane, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, hk,
      decide_true, Bool.true_and]
    by_cases h1 : i * lb ≤ k <;> by_cases h2 : k < i * lb + lb
    · have h3 : k - i * lb < lb := by omega
      simp [h1, h2, h3, show ¬ k < i * lb by omega, show k - i * lb < w by omega]
    · have h3 : ¬ k - i * lb < lb := by omega
      simp [h1, h2, h3, show ¬ k < i * lb by omega, BitVec.getLsbD_of_ge y (k - i * lb) (by omega)]
    · simp [h1, h2, show k < i * lb by omega]
    · omega
  · rw [BitVec.getLsbD_of_ge _ k (Nat.le_of_not_lt hk), BitVec.getLsbD_of_ge _ k (Nat.le_of_not_lt hk)]
    simp [hk]

/-- Reading back the replaced lane. -/
theorem lane_setLane_same (lb : Nat) (x : BitVec w) (i : Nat) (y : BitVec lb)
    (h : i * lb + lb ≤ w) : lane lb (setLane lb x i y) i = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [getLsbD_lane, getLsbD_setLane]
  simp [hk, show i * lb + k < w by omega]

/-- The other lanes are unchanged. -/
theorem lane_setLane_ne (lb : Nat) (x : BitVec w) {i j : Nat} (y : BitVec lb) (h : i ≠ j) :
    lane lb (setLane lb x i y) j = lane lb x j := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [getLsbD_lane, getLsbD_lane, getLsbD_setLane]
  have : ¬ (i * lb ≤ j * lb + k ∧ j * lb + k < i * lb + lb) := by
    rintro ⟨h1, h2⟩
    rcases Nat.lt_or_gt_of_ne h with hij | hij
    · have : (i + 1) * lb ≤ j * lb := Nat.mul_le_mul_right lb hij
      rw [Nat.succ_mul] at this; omega
    · have : (j + 1) * lb ≤ i * lb := Nat.mul_le_mul_right lb hij
      rw [Nat.succ_mul] at this; omega
  simp [this]

/-- Two vectors with the same lanes are equal (`n` lanes of `lb` bits cover the width). -/
theorem ext_lane (lb n : Nat) {x y : BitVec w} (hw : w = n * lb)
    (h : ∀ i, i < n → lane lb x i = lane lb y i) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hlb : 0 < lb := by
    rcases Nat.eq_zero_or_pos lb with h0 | h0
    · subst h0; simp at hw; omega
    · exact h0
  have hi : k / lb < n := by
    rw [Nat.div_lt_iff_lt_mul hlb]; omega
  have := congrArg (fun v => v.getLsbD (k % lb)) (h (k / lb) hi)
  simp only [getLsbD_lane, Nat.mod_lt k hlb, decide_true, Bool.true_and] at this
  rwa [show k / lb * lb + k % lb = k by rw [Nat.mul_comm]; exact Nat.div_add_mod k lb] at this

/-- Byte `j` of lane `i` is byte `i·(lb/8) + j` of the vector (little-endian memory layout of
the lanes), for byte-sized lanes. -/
theorem byte_lane (x : BitVec w) {lb : Nat} (i j : Nat) (hlb : lb % 8 = 0) (hj : j < lb / 8) :
    byte (lane lb x i) j = byte x (i * (lb / 8) + j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [byte, getLsbD_lane, hk, decide_true, Bool.true_and]
  have h1 : j * 8 + k < lb := by omega
  have h2 : i * lb + (j * 8 + k) = (i * (lb / 8) + j) * 8 + k := by
    have : lb = lb / 8 * 8 := by omega
    rw [Nat.add_mul, Nat.mul_assoc, ← this]; omega
  simp [h1, h2]

/-- Little-endian `bitcast` keeps every byte. -/
theorem byte_bitcastLE (h : w = w') (x : BitVec w) (j : Nat) :
    byte (bitcastLE h x) j = byte x j := by
  subst h; rfl

/-- Little-endian `bitcast` is invertible. -/
theorem bitcastLE_bitcastLE (h : w = w') (x : BitVec w) :
    bitcastLE h.symm (bitcastLE h x) = x := by
  subst h; rfl

end Vec

/-! ## Non-vacuity witnesses -/

/-- `i64x2` with lanes `[1, 2]`: lane 1 is `2`, the bytes of lane 1 start at byte 8. -/
example : Vec.lane 64 (0x0000000000000002_0000000000000001#128) 1 = 2#64 := by decide

example : Vec.byte (0x0000000000000002_0000000000000001#128) 8 = 2#8 := by decide

/-- `insertlane`-style update of lane 2 of an `i32x4`, then read back. -/
example : Vec.setLane 32 (0x44444444_33333333_22222222_11111111#128) 2 0xabcdef01#32 =
    0x44444444_abcdef01_22222222_11111111#128 := by decide

example : Vec.lane 32 (Vec.setLane 32 (0#128) 3 7#32) 3 = 7#32 :=
  Vec.lane_setLane_same 32 _ 3 _ (by decide)

/-- An `i64x2` read as `i32x4` (little-endian `bitcast`): lane 2 is the low half of lane 1. -/
example : Vec.lane 32 (Vec.bitcastLE rfl (0x0000000000000002_0000000000000001#128)) 2 = 2#32 := by
  decide

example : VShape.ofName? "i64x2" = some .i64x2 := by decide
example : VShape.i32x4.width = 128 ∧ VShape.i8x8.width = 64 := by decide

/-- `lane_setLane_ne`, `ext_lane` and `byte_lane` at concrete vectors (their premises hold). -/
example : Vec.lane 32 (Vec.setLane 32 (0x44444444_33333333_22222222_11111111#128) 1 5#32) 0 =
    0x11111111#32 :=
  (Vec.lane_setLane_ne 32 _ _ (by decide)).trans (by decide)

example : (0x0000000000000002_0000000000000001#128) =
    Vec.setLane 64 (Vec.setLane 64 0#128 0 1#64) 1 2#64 :=
  Vec.ext_lane 64 2 rfl (by intro i hi; rcases i with _ | _ | i <;> first | decide | omega)

example : Vec.byte (Vec.lane 64 (0x0000000000000002_0000000000000001#128) 1) 0 =
    Vec.byte (0x0000000000000002_0000000000000001#128) 8 :=
  Vec.byte_lane _ (lb := 64) 1 0 (by decide) (by decide)

end Clif
