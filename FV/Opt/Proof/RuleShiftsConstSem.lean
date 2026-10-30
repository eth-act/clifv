import FV.Clif.Sem
import FV.Isle.Opt.Helpers

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option Elab.async false

namespace Opt.Proof
open Isle Isle.Opt Clif
attribute [local implicit_reducible] Ty.width

/-- The unsigned mask observes precisely the low log2(width) bits, even after a u64 cast. -/
theorem shifts_const_mask (t : Ty) (n : Nat) :
    Rust.band64 (n : Int) ((t.width : Int) - 1) = (n % t.width : Nat) := by
  have hp : 2 ^ t.width.log2 = t.width := by cases t <;> decide
  have hw : 0 < t.width := by cases t <;> decide
  have hb : t.width - 1 < 2 ^ 64 := by cases t <;> decide
  have hd : t.width ∣ 2 ^ 64 := by cases t <;> decide
  have he : (t.width : Int) - 1 = ((t.width - 1 : Nat) : Int) := by omega
  simp only [Rust.band64, he, BitVec.ofInt_natCast, BitVec.toNat_and,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  rw [← hp, Nat.and_two_pow_sub_one_eq_mod, hp, Nat.mod_mod_of_dvd _ hd]

/-- Neither of the masked summands can cause a u64 addition overflow. -/
theorem shifts_const_sum (t : Ty) (a b : Nat) :
    Rust.asU64 ((a % t.width : Nat) + (b % t.width : Nat)) =
      ((a % t.width + b % t.width : Nat) : Int) := by
  have hw : 0 < t.width := by cases t <;> decide
  have hb : t.width ≤ 128 := by cases t <;> decide
  have ha := Nat.mod_lt a hw
  have hc := Nat.mod_lt b hw
  rw [← Int.natCast_add, Rust.asU64, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]

/-- The combined amount fits in every legal amount type, including i8 for i128 data. -/
theorem shifts_const_amount (t k : Ty) (n : Nat) (hn : n < t.width) :
    Sem.shiftAmt t.width (BitVec.ofInt k.width (n : Int)) = n := by
  have hk : t.width ≤ 2 ^ k.width := by cases t <;> cases k <;> decide
  simp only [Sem.shiftAmt, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hn hk), Nat.mod_eq_of_lt hn]

/-- Logical right shifts compose symbolically; no variable-shift SAT circuit is needed. -/
theorem shifts_const_ushr {t a b : Ty} (x : BitVec t.width)
    (u : BitVec a.width) (v : BitVec b.width)
    (h : u.toNat % t.width + v.toNat % t.width < t.width) :
    Sem.ushr (Sem.ushr x u) v =
      Sem.ushr x (BitVec.ofInt a.width ((u.toNat % t.width + v.toNat % t.width : Nat) : Int)) := by
  simp only [Sem.ushr]
  rw [shifts_const_amount t a _ h]
  simp only [Sem.shiftAmt]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_add]

/-- Arithmetic right shifts compose at every width, including a signed i128 minimum. -/
theorem shifts_const_sshr {t a b : Ty} (x : BitVec t.width)
    (u : BitVec a.width) (v : BitVec b.width)
    (h : u.toNat % t.width + v.toNat % t.width < t.width) :
    Sem.sshr (Sem.sshr x u) v =
      Sem.sshr x (BitVec.ofInt a.width ((u.toNat % t.width + v.toNat % t.width : Nat) : Int)) := by
  simp only [Sem.sshr]
  rw [shifts_const_amount t a _ h]
  simp only [Sem.shiftAmt, BitVec.sshiftRight_add]

/-- Two left shifts whose masked sum reaches the width lose every source bit. -/
theorem shifts_const_ishl_zero {t a b : Ty} (x : BitVec t.width)
    (u : BitVec a.width) (v : BitVec b.width)
    (h : t.width ≤ u.toNat % t.width + v.toNat % t.width) :
    Sem.ishl (Sem.ishl x u) v = 0#t.width := by
  simp only [Sem.ishl, Sem.shiftAmt, ← BitVec.shiftLeft_add]
  exact BitVec.shiftLeft_eq_zero h

/-- Two logical right shifts whose masked sum reaches the width lose every source bit. -/
theorem shifts_const_ushr_zero {t a b : Ty} (x : BitVec t.width)
    (u : BitVec a.width) (v : BitVec b.width)
    (h : t.width ≤ u.toNat % t.width + v.toNat % t.width) :
    Sem.ushr (Sem.ushr x u) v = 0#t.width := by
  have he : (x >>> (u.toNat % t.width)) >>> (v.toNat % t.width) =
      x >>> (u.toNat % t.width + v.toNat % t.width) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_add]
  simpa only [Sem.ushr, Sem.shiftAmt, he] using
    (BitVec.ushiftRight_eq_zero (x := x) h)

-- Each symbolic helper has a concrete instance; these include unsigned wrapping
-- presentations, differing amount widths, zero, width-1, width and 2*width-2 sums.
example : Rust.band64 (18446744073709551615 : Int) ((Ty.i128.width : Int) - 1) = 127 :=
  shifts_const_mask .i128 18446744073709551615
example : Rust.asU64 ((127 : Int) + 127) = 254 := shifts_const_sum .i128 255 65535
example : Sem.shiftAmt 128 (BitVec.ofInt 8 127) = 127 :=
  shifts_const_amount .i128 .i8 127 (by decide)
example : Sem.ushr (Sem.ushr (255#8) (248#8)) (65528#16) =
    Sem.ushr (255#8) (BitVec.ofInt 8 0) :=
  shifts_const_ushr (t := .i8) (a := .i8) (b := .i16) _ _ _ (by decide)
example : Sem.sshr (Sem.sshr (0x80000000000000000000000000000000#128) (255#8)) (128#64) =
    Sem.sshr (0x80000000000000000000000000000000#128) (BitVec.ofInt 8 127) :=
  shifts_const_sshr (t := .i128) (a := .i8) (b := .i64) _ _ _ (by decide)
example : Sem.ishl (Sem.ishl (0x80000000000000000000000000000001#128) (255#8)) (129#16) = 0#128 :=
  shifts_const_ishl_zero (t := .i128) (a := .i8) (b := .i16) _ _ _ (by decide)
example : Sem.ushr (Sem.ushr (0xffffffffffffffffffffffffffffffff#128) (255#8)) (65535#16) = 0#128 :=
  shifts_const_ushr_zero (t := .i128) (a := .i8) (b := .i16) _ _ _ (by decide)

end Opt.Proof
