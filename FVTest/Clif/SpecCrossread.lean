import FV.Clif
import Std.Tactic.BVDecide

/-!
# Cross-read of `Clif.Sem` against the VeriISLE CLIF specs

Each `Spec.*` definition below transcribes the `(spec ...)` of an opcode in
`third_party/wasmtime/cranelift/codegen/src/spec/inst_specs.isle` (Cranelift 0.136.1), with
the SMT-LIB meaning of its primitives:

* `bvudiv`/`bvurem`/`bvsdiv`/`bvsrem` follow the SMT-LIB definitions (`bvudiv x 0 = ~0`,
  `bvurem x 0 = x`, signed versions via absolute values);
* `clz`, `rev`, `popcnt`, `rotl`, `rotr` follow the encodings of the VeriISLE solver
  (`cranelift/isle/veri/veri/src/encoded/{clz,rev,popcnt}.rs` and `encode_rotate` in
  `solver.rs`);
* `conv_to` to a narrower width is `extract (w-1) 0`; `zero_ext`/`sign_ext` are SMT-LIB
  `zero_extend`/`sign_extend`; SMT-LIB comparisons are on `toNat`/`toInt`;
* traps: a spec that sets `clif_trap` is modelled by `SpecOut.trap`; the trap code is not
  part of VeriISLE.

The theorems state agreement for every width the spec is instantiated at (i8..i64, and all
shift-amount widths). `docs/contracts/clif-spec-crossread.md` lists them per opcode.
-/

namespace Clif.SpecCrossread

open Clif

/-! ## SMT-LIB and VeriISLE primitives -/

/-- Outcome of a spec with `(modifies clif_trap)`. -/
inductive SpecOut (w : Nat) where
  | trap
  | val (r : BitVec w)
  deriving DecidableEq

/-- Forget the trap code (VeriISLE only knows whether a trap happens). -/
def toSpec {w : Nat} : Except TrapCode (BitVec w) → SpecOut w
  | .error _ => .trap
  | .ok r => .val r

variable {w : Nat}

def bvudiv (s t : BitVec w) : BitVec w := if t = 0 then BitVec.allOnes w else s / t
def bvurem (s t : BitVec w) : BitVec w := if t = 0 then s else s % t
def bvsdiv (s t : BitVec w) : BitVec w :=
  if !s.msb && !t.msb then bvudiv s t
  else if s.msb && !t.msb then -(bvudiv (-s) t)
  else if !s.msb && t.msb then -(bvudiv s (-t))
  else bvudiv (-s) (-t)
def bvsrem (s t : BitVec w) : BitVec w :=
  if !s.msb && !t.msb then bvurem s t
  else if s.msb && !t.msb then -(bvurem (-s) t)
  else if !s.msb && t.msb then bvurem s (-t)
  else -(bvurem (-s) (-t))

/-- `bv_is_zero!` -/
abbrev bvIsZero (x : BitVec w) : Prop := x = 0

/-- `bv_top_bit_set!` -/
abbrev bvTopBitSet (w : Nat) : BitVec w := BitVec.twoPow w (w - 1)

/-- `(macro (shift_amount x y) (conv_to (widthof x) (bvand (zero_ext 64 y)
(bvsub (int2bv 64 (widthof x)) #x0000000000000001))))` -/
def shiftAmount (w : Nat) {v : Nat} (y : BitVec v) : BitVec w :=
  ((y.zeroExtend 64) &&& (BitVec.ofNat 64 w - 1#64)).setWidth w

/-- `encode_rotate Left`: `(bvor (bvshl x a') (bvlshr x (bvsub w a')))`, `a' = bvurem a w`. -/
def rotl (x a : BitVec w) : BitVec w :=
  let a' := a % BitVec.ofNat w w
  (x <<< a') ||| (x >>> (BitVec.ofNat w w - a'))

/-- `encode_rotate Right`: `(bvor (bvshl x (bvsub w a')) (bvlshr x a'))`. -/
def rotr (x a : BitVec w) : BitVec w :=
  let a' := a % BitVec.ofNat w w
  (x <<< (BitVec.ofNat w w - a')) ||| (x >>> a')

/-- `encoded/clz.rs`: binary search over the shift amounts `shifts` (`w/2, …, 1`); each
round adds `s` to the count iff `x >> s = 0` (and otherwise continues with `x >> s`); the
last round adds 1 iff the remaining value is 0. -/
def clzRounds : List Nat → BitVec w → BitVec w
  | [], x => if x != 0 then 0 else 1
  | s :: ss, x =>
    let y := x >>> s
    if y != 0 then clzRounds ss y else BitVec.ofNat w s + clzRounds ss x

def clzShifts : Nat → List Nat
  | 8 => [4, 2, 1] | 16 => [8, 4, 2, 1] | 32 => [16, 8, 4, 2, 1]
  | 64 => [32, 16, 8, 4, 2, 1] | _ => []

def clz (x : BitVec w) : BitVec w := clzRounds (clzShifts w) x

/-- `encoded/rev.rs`: swap halves, then swap adjacent blocks of `s` bits using the masks
`hi`/`lo` for `s = w/4, …, 1`. -/
def revRounds (x : BitVec w) (rounds : List (Nat × BitVec w × BitVec w)) : BitVec w :=
  rounds.foldl (fun x (s, hi, lo) => ((x &&& hi) >>> s) ||| ((x &&& lo) <<< s))
    ((x >>> (w / 2)) ||| (x <<< (w / 2)))

def rev8 (x : BitVec 8) : BitVec 8 := revRounds x [(2, 0xcc, 0x33), (1, 0xaa, 0x55)]
def rev16 (x : BitVec 16) : BitVec 16 :=
  revRounds x [(4, 0xf0f0, 0x0f0f), (2, 0xcccc, 0x3333), (1, 0xaaaa, 0x5555)]
def rev32 (x : BitVec 32) : BitVec 32 :=
  revRounds x [(8, 0xff00ff00, 0x00ff00ff), (4, 0xf0f0f0f0, 0x0f0f0f0f),
    (2, 0xcccccccc, 0x33333333), (1, 0xaaaaaaaa, 0x55555555)]
def rev64 (x : BitVec 64) : BitVec 64 :=
  revRounds x [(16, 0xffff0000ffff0000, 0x0000ffff0000ffff),
    (8, 0xff00ff00ff00ff00, 0x00ff00ff00ff00ff), (4, 0xf0f0f0f0f0f0f0f0, 0x0f0f0f0f0f0f0f0f),
    (2, 0xcccccccccccccccc, 0x3333333333333333), (1, 0xaaaaaaaaaaaaaaaa, 0x5555555555555555)]

/-- `encoded/popcnt.rs`: the sum of the bits of `x` in `k = log2 w + 1` bits, zero-extended. -/
def popSum (k : Nat) (x : BitVec w) : Nat → BitVec k
  | 0 => 0
  | i + 1 => popSum k x i + (x.extractLsb' i 1).zeroExtend k

def popcnt (k : Nat) (x : BitVec w) : BitVec w := (popSum k x w).zeroExtend w

/-! ## Transcribed specs (`inst_specs.isle`) -/

namespace Spec

def iadd (x y : BitVec w) : BitVec w := x + y           -- (bvadd x y)
def isub (x y : BitVec w) : BitVec w := x - y           -- (bvsub x y)
def ineg (x : BitVec w) : BitVec w := -x                -- (bvneg x)
def imul (x y : BitVec w) : BitVec w := x * y           -- (bvmul x y)
def band (x y : BitVec w) : BitVec w := x &&& y         -- (bvand x y)
def bor (x y : BitVec w) : BitVec w := x ||| y          -- (bvor x y)
def bxor (x y : BitVec w) : BitVec w := x ^^^ y         -- (bvxor x y)
def bnot (x : BitVec w) : BitVec w := ~~~x              -- (bvnot x)

/-- `(with (low) (= (concat result low) (bvmul xwide ywide)))`, `xwide = zero_ext 2w x`. -/
def umulhiRel (x y r : BitVec w) : Prop :=
  ∃ low : BitVec w, r ++ low = x.zeroExtend (w + w) * y.zeroExtend (w + w)
/-- As `umulhiRel` with `sign_ext`. -/
def smulhiRel (x y r : BitVec w) : Prop :=
  ∃ low : BitVec w, r ++ low = x.signExtend (w + w) * y.signExtend (w + w)

def udiv (x y : BitVec w) : SpecOut w :=
  if bvIsZero y then .trap else .val (bvudiv x y)
def sdiv (x y : BitVec w) : SpecOut w :=
  if bvIsZero y then .trap
  else if x = bvTopBitSet w ∧ bvIsZero (~~~y) then .trap
  else .val (bvsdiv x y)
def urem (x y : BitVec w) : SpecOut w :=
  if bvIsZero y then .trap else .val (bvurem x y)
def srem (x y : BitVec w) : SpecOut w :=
  if bvIsZero y then .trap else .val (bvsrem x y)

def ishl {v : Nat} (x : BitVec w) (y : BitVec v) : BitVec w := x <<< shiftAmount w y
def ushr {v : Nat} (x : BitVec w) (y : BitVec v) : BitVec w := x >>> shiftAmount w y
def sshr {v : Nat} (x : BitVec w) (y : BitVec v) : BitVec w := x.sshiftRight' (shiftAmount w y)
def rotl {v : Nat} (x : BitVec w) (y : BitVec v) : BitVec w :=
  SpecCrossread.rotl x (shiftAmount w y)
def rotr {v : Nat} (x : BitVec w) (y : BitVec v) : BitVec w :=
  SpecCrossread.rotr x (shiftAmount w y)

def clz (x : BitVec w) : BitVec w := SpecCrossread.clz x

/-- `(match cc ((Equal) (= x y)) ...)` with SMT-LIB comparisons (on integers). -/
def icmpHolds (cc : IntCC) (x y : BitVec w) : Prop :=
  match cc with
  | .eq => x = y
  | .ne => ¬ x = y
  | .sgt => x.toInt > y.toInt
  | .sge => x.toInt ≥ y.toInt
  | .slt => x.toInt < y.toInt
  | .sle => x.toInt ≤ y.toInt
  | .ugt => x.toNat > y.toNat
  | .uge => x.toNat ≥ y.toNat
  | .ult => x.toNat < y.toNat
  | .ule => x.toNat ≤ y.toNat

instance (cc : IntCC) (x y : BitVec w) : Decidable (icmpHolds cc x y) := by
  cases cc <;> unfold icmpHolds <;> infer_instance

def icmp (cc : IntCC) (x y : BitVec w) : BitVec 8 := if icmpHolds cc x y then 0x01 else 0x00

/-- `(zero_ext (widthof result) x)`: SMT-LIB `zero_extend`. -/
def uextend (v : Nat) (x : BitVec w) : BitVec (v - w + w) := 0#(v - w) ++ x
/-- `(sign_ext (widthof result) x)`: SMT-LIB `sign_extend` (copies of the sign bit). -/
def sextend (v : Nat) (x : BitVec w) : BitVec (v - w + w) :=
  (if x.msb then BitVec.allOnes (v - w) else 0#(v - w)) ++ x
/-- `(conv_to (widthof result) x)` to a narrower width: `extract (v-1) 0`. -/
def ireduce (v : Nat) (x : BitVec w) : BitVec v := x.extractLsb' 0 v

/-- `(macro (effective_address p offset) (bvadd p (sign_ext 64 offset)))`. -/
def effectiveAddress (p : BitVec 64) (offset : BitVec 32) : BitVec 64 :=
  p + offset.signExtend 64

/-! Non-E specs cross-read as well: `iabs`, `smin`/`umin`/`smax`/`umax`, `bitselect`,
`uadd_overflow_trap`. -/

def iabs (x : BitVec w) : BitVec w := if x.toInt ≥ (0#w).toInt then x else -x
def smin (x y : BitVec w) : BitVec w := if x.toInt ≤ y.toInt then x else y
def umin (x y : BitVec w) : BitVec w := if x.toNat ≤ y.toNat then x else y
def smax (x y : BitVec w) : BitVec w := if x.toInt ≥ y.toInt then x else y
def umax (x y : BitVec w) : BitVec w := if x.toNat ≥ y.toNat then x else y
def bitselect (c x y : BitVec w) : BitVec w := (c &&& x) ||| (~~~c &&& y)

/-- `uadd_overflow_trap` (32/64 only): carry out of the 65-bit sum traps. -/
def uaddOverflowTrap (x y : BitVec w) : SpecOut w :=
  let sum := x.zeroExtend 65 + y.zeroExtend 65
  if sum.getLsbD w then .trap else .val (sum.setWidth w)

end Spec

/-! ## Agreement: generic lemmas -/

theorem iadd_eq (x y : BitVec w) : Sem.iadd x y = Spec.iadd x y := rfl
theorem isub_eq (x y : BitVec w) : Sem.isub x y = Spec.isub x y := rfl
theorem ineg_eq (x : BitVec w) : Sem.ineg x = Spec.ineg x := rfl
theorem imul_eq (x y : BitVec w) : Sem.imul x y = Spec.imul x y := rfl
theorem band_eq (x y : BitVec w) : Sem.band x y = Spec.band x y := rfl
theorem bor_eq (x y : BitVec w) : Sem.bor x y = Spec.bor x y := rfl
theorem bxor_eq (x y : BitVec w) : Sem.bxor x y = Spec.bxor x y := rfl
theorem bnot_eq (x : BitVec w) : Sem.bnot x = Spec.bnot x := rfl
theorem bitselect_eq (c x y : BitVec w) : Sem.bitselect c x y = Spec.bitselect c x y := rfl

/-- `umulhi` satisfies the spec relation. -/
theorem umulhi_spec (x y : BitVec w) : Spec.umulhiRel x y (Sem.umulhi x y) :=
  ⟨_, BitVec.extractLsb'_append_extractLsb'⟩

theorem smulhi_spec (x y : BitVec w) : Spec.smulhiRel x y (Sem.smulhi x y) :=
  ⟨_, BitVec.extractLsb'_append_extractLsb'⟩

theorem append_left_inj {v : Nat} {a b : BitVec w} {c d : BitVec v} (h : a ++ c = b ++ d) :
    a = b := by
  have := congrArg (BitVec.extractLsb' v w) h
  simpa [BitVec.extractLsb'_append_eq_left] using this

/-- The spec relation determines the `umulhi` result. -/
theorem umulhi_unique (x y r : BitVec w) (h : Spec.umulhiRel x y r) : r = Sem.umulhi x y := by
  obtain ⟨low, hl⟩ := h
  obtain ⟨low', hl'⟩ := umulhi_spec x y
  exact append_left_inj (hl.trans hl'.symm)

theorem smulhi_unique (x y r : BitVec w) (h : Spec.smulhiRel x y r) : r = Sem.smulhi x y := by
  obtain ⟨low, hl⟩ := h
  obtain ⟨low', hl'⟩ := smulhi_spec x y
  exact append_left_inj (hl.trans hl'.symm)

theorem icmp_eq (cc : IntCC) (x y : BitVec w) : Sem.icmp cc x y = Spec.icmp cc x y := by
  cases cc <;>
    simp [Sem.icmp, Sem.intcc, Sem.bool8, Spec.icmp, Spec.icmpHolds, BitVec.slt, BitVec.sle,
      BitVec.ult, BitVec.ule] <;> omega

theorem smin_eq (x y : BitVec w) : Sem.smin x y = Spec.smin x y := by
  simp [Sem.smin, Spec.smin, BitVec.sle]
theorem smax_eq (x y : BitVec w) : Sem.smax x y = Spec.smax x y := by
  simp [Sem.smax, Spec.smax, BitVec.sle]
theorem umin_eq (x y : BitVec w) : Sem.umin x y = Spec.umin x y := by
  simp [Sem.umin, Spec.umin, BitVec.ule]
theorem umax_eq (x y : BitVec w) : Sem.umax x y = Spec.umax x y := by
  simp [Sem.umax, Spec.umax, BitVec.ule]

theorem iabs_eq (x : BitVec w) : Sem.iabs x = Spec.iabs x := by
  unfold Sem.iabs Spec.iabs
  rw [BitVec.msb_eq_toInt]
  by_cases h : x.toInt < 0
  · have h' : ¬ x.toInt ≥ (0#w).toInt := by simp; omega
    rw [ite_eq_right h']; simp [h]
  · have h' : x.toInt ≥ (0#w).toInt := by simp; omega
    rw [ite_eq_left h']; simp [h]

/-- The spec's `shift_amount` is `y mod w` for `w = 2^k ≤ 64` and amounts of width `≤ 64`. -/
theorem shiftAmount_toNat {v : Nat} (k : Nat) (y : BitVec v) (hv : v ≤ 64) (hk : k ≤ 6) :
    (shiftAmount (2 ^ k) y).toNat = Sem.shiftAmt (2 ^ k) y := by
  have hk' : 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by omega) hk
  have hy : y.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by omega) hv)
  have h1 : (BitVec.ofNat 64 (2 ^ k) - 1#64).toNat = 2 ^ k - 1 := by
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have : 2 ^ k % 2 ^ 64 = 2 ^ k := Nat.mod_eq_of_lt (by omega)
    omega
  unfold shiftAmount Sem.shiftAmt
  rw [BitVec.toNat_setWidth, BitVec.toNat_and, h1, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt hy, Nat.and_two_pow_sub_one_eq_mod]
  apply Nat.mod_eq_of_lt
  have : y.toNat % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  have : 2 ^ k ≤ 2 ^ (2 ^ k) := Nat.pow_le_pow_right (by omega) (Nat.le_of_lt Nat.lt_two_pow_self)
  omega

theorem shiftAmount_lt {v : Nat} (k : Nat) (y : BitVec v) (hv : v ≤ 64) (hk : k ≤ 6) :
    (shiftAmount (2 ^ k) y).toNat < 2 ^ k := by
  rw [shiftAmount_toNat k y hv hk]
  exact Nat.mod_lt _ (Nat.two_pow_pos k)

theorem ishl_eq {v : Nat} (k : Nat) (x : BitVec (2 ^ k)) (y : BitVec v) (hv : v ≤ 64)
    (hk : k ≤ 6) : Sem.ishl x y = Spec.ishl x y := by
  unfold Sem.ishl Spec.ishl
  rw [BitVec.shiftLeft_eq', shiftAmount_toNat k y hv hk]

theorem ushr_eq {v : Nat} (k : Nat) (x : BitVec (2 ^ k)) (y : BitVec v) (hv : v ≤ 64)
    (hk : k ≤ 6) : Sem.ushr x y = Spec.ushr x y := by
  unfold Sem.ushr Spec.ushr
  rw [BitVec.ushiftRight_eq', shiftAmount_toNat k y hv hk]

theorem sshr_eq {v : Nat} (k : Nat) (x : BitVec (2 ^ k)) (y : BitVec v) (hv : v ≤ 64)
    (hk : k ≤ 6) : Sem.sshr x y = Spec.sshr x y := by
  unfold Sem.sshr Spec.sshr
  rw [BitVec.sshiftRight_eq', shiftAmount_toNat k y hv hk]

theorem rotl_encode (x a : BitVec w) (h : a.toNat < w) :
    x.rotateLeft a.toNat = SpecCrossread.rotl x a := by
  have hw : w < 2 ^ w := Nat.lt_two_pow_self
  have hm : a % BitVec.ofNat w w = a := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt h]
  unfold SpecCrossread.rotl
  simp only [hm]
  rw [BitVec.rotateLeft_def, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', Nat.mod_eq_of_lt h]
  congr 2
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw,
    show 2 ^ w - a.toNat + w = (w - a.toNat) + 2 ^ w by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

theorem rotr_encode (x a : BitVec w) (h : a.toNat < w) :
    x.rotateRight a.toNat = SpecCrossread.rotr x a := by
  have hw : w < 2 ^ w := Nat.lt_two_pow_self
  have hm : a % BitVec.ofNat w w = a := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt h]
  unfold SpecCrossread.rotr
  simp only [hm]
  rw [BitVec.rotateRight_def, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', Nat.mod_eq_of_lt h,
    BitVec.or_comm]
  congr 2
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw,
    show 2 ^ w - a.toNat + w = (w - a.toNat) + 2 ^ w by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

theorem rotl_eq {v : Nat} (k : Nat) (x : BitVec (2 ^ k)) (y : BitVec v) (hv : v ≤ 64)
    (hk : k ≤ 6) : Sem.rotl x y = Spec.rotl x y := by
  unfold Sem.rotl Spec.rotl
  rw [← shiftAmount_toNat k y hv hk]
  exact rotl_encode x _ (shiftAmount_lt k y hv hk)

theorem rotr_eq {v : Nat} (k : Nat) (x : BitVec (2 ^ k)) (y : BitVec v) (hv : v ≤ 64)
    (hk : k ≤ 6) : Sem.rotr x y = Spec.rotr x y := by
  unfold Sem.rotr Spec.rotr
  rw [← shiftAmount_toNat k y hv hk]
  exact rotr_encode x _ (shiftAmount_lt k y hv hk)

theorem udiv_eq (x y : BitVec w) : toSpec (Sem.udiv x y) = Spec.udiv x y := by
  unfold Sem.udiv Spec.udiv bvudiv
  by_cases h : y = 0
  · rw [ite_eq_left h, ite_eq_left h]; rfl
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h]; rfl

theorem urem_eq (x y : BitVec w) : toSpec (Sem.urem x y) = Spec.urem x y := by
  unfold Sem.urem Spec.urem bvurem
  by_cases h : y = 0
  · rw [ite_eq_left h, ite_eq_left h]; rfl
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h]; rfl

/-- The spec's `iconst` relation `(= arg (zero_ext 64 result))` holds for the reader's
immediate (the zero-extended bits of our constant) and determines the result, for widths
`≤ 64`. -/
theorem iconst_spec (r : BitVec w) (hw : w ≤ 64) :
    ∀ r' : BitVec w, r.zeroExtend 64 = r'.zeroExtend 64 → r' = r := by
  intro r' h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth] at this
  have h1 : r.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le r.isLt (Nat.pow_le_pow_right (by omega) hw)
  have h2 : r'.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le r'.isLt (Nat.pow_le_pow_right (by omega) hw)
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
  exact (BitVec.eq_of_toNat_eq this).symm

/-- Effective address of a load/store with an `i64` pointer and an `Offset32`: the spec's
`(bvadd p (sign_ext 64 offset))` equals `Clif.effAddr`. -/
theorem effAddr_eq (p : BitVec 64) (off : Int) (h1 : -2 ^ 31 ≤ off) (h2 : off < 2 ^ 31) :
    effAddr ⟨.i64, p⟩ off = (Spec.effectiveAddress p (BitVec.ofInt 32 off)).toNat := by
  have : (BitVec.ofInt 32 off).signExtend 64 = BitVec.ofInt 64 off := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_ofInt, BitVec.toInt_ofInt]
    simp only [Int.bmod]
    omega
  unfold Spec.effectiveAddress
  rw [this]
  simp only [effAddr, Val.toNat, BitVec.toNat_add, BitVec.toNat_ofInt, Ty.width]
  omega

/-- `trap`: `(provide clif_trap)`. -/
theorem trap_eq (env : Env) (p : Program) (s : State) (c : TrapCode) :
    stepTerm env p s (.trap c) = .trapped c := rfl

/-! ## Agreement per width (i8, i16, i32, i64) -/

section PerWidth

theorem iadd_i8 (x y : BitVec 8) : Sem.iadd x y = Spec.iadd x y := iadd_eq x y
theorem iadd_i16 (x y : BitVec 16) : Sem.iadd x y = Spec.iadd x y := iadd_eq x y
theorem iadd_i32 (x y : BitVec 32) : Sem.iadd x y = Spec.iadd x y := iadd_eq x y
theorem iadd_i64 (x y : BitVec 64) : Sem.iadd x y = Spec.iadd x y := iadd_eq x y
theorem iadd_i128 (x y : BitVec 128) : Sem.iadd x y = Spec.iadd x y := iadd_eq x y
theorem isub_i8 (x y : BitVec 8) : Sem.isub x y = Spec.isub x y := isub_eq x y
theorem isub_i16 (x y : BitVec 16) : Sem.isub x y = Spec.isub x y := isub_eq x y
theorem isub_i32 (x y : BitVec 32) : Sem.isub x y = Spec.isub x y := isub_eq x y
theorem isub_i64 (x y : BitVec 64) : Sem.isub x y = Spec.isub x y := isub_eq x y
theorem ineg_i8 (x : BitVec 8) : Sem.ineg x = Spec.ineg x := ineg_eq x
theorem ineg_i16 (x : BitVec 16) : Sem.ineg x = Spec.ineg x := ineg_eq x
theorem ineg_i32 (x : BitVec 32) : Sem.ineg x = Spec.ineg x := ineg_eq x
theorem ineg_i64 (x : BitVec 64) : Sem.ineg x = Spec.ineg x := ineg_eq x
theorem imul_i8 (x y : BitVec 8) : Sem.imul x y = Spec.imul x y := imul_eq x y
theorem imul_i16 (x y : BitVec 16) : Sem.imul x y = Spec.imul x y := imul_eq x y
theorem imul_i32 (x y : BitVec 32) : Sem.imul x y = Spec.imul x y := imul_eq x y
theorem imul_i64 (x y : BitVec 64) : Sem.imul x y = Spec.imul x y := imul_eq x y
theorem band_i8 (x y : BitVec 8) : Sem.band x y = Spec.band x y := band_eq x y
theorem band_i16 (x y : BitVec 16) : Sem.band x y = Spec.band x y := band_eq x y
theorem band_i32 (x y : BitVec 32) : Sem.band x y = Spec.band x y := band_eq x y
theorem band_i64 (x y : BitVec 64) : Sem.band x y = Spec.band x y := band_eq x y
theorem bor_i8 (x y : BitVec 8) : Sem.bor x y = Spec.bor x y := bor_eq x y
theorem bor_i16 (x y : BitVec 16) : Sem.bor x y = Spec.bor x y := bor_eq x y
theorem bor_i32 (x y : BitVec 32) : Sem.bor x y = Spec.bor x y := bor_eq x y
theorem bor_i64 (x y : BitVec 64) : Sem.bor x y = Spec.bor x y := bor_eq x y
theorem bxor_i8 (x y : BitVec 8) : Sem.bxor x y = Spec.bxor x y := bxor_eq x y
theorem bxor_i16 (x y : BitVec 16) : Sem.bxor x y = Spec.bxor x y := bxor_eq x y
theorem bxor_i32 (x y : BitVec 32) : Sem.bxor x y = Spec.bxor x y := bxor_eq x y
theorem bxor_i64 (x y : BitVec 64) : Sem.bxor x y = Spec.bxor x y := bxor_eq x y
theorem bnot_i8 (x : BitVec 8) : Sem.bnot x = Spec.bnot x := bnot_eq x
theorem bnot_i16 (x : BitVec 16) : Sem.bnot x = Spec.bnot x := bnot_eq x
theorem bnot_i32 (x : BitVec 32) : Sem.bnot x = Spec.bnot x := bnot_eq x
theorem bnot_i64 (x : BitVec 64) : Sem.bnot x = Spec.bnot x := bnot_eq x

theorem umulhi_i8 (x y : BitVec 8) : Spec.umulhiRel x y (Sem.umulhi x y) := umulhi_spec x y
theorem umulhi_i16 (x y : BitVec 16) : Spec.umulhiRel x y (Sem.umulhi x y) := umulhi_spec x y
theorem umulhi_i32 (x y : BitVec 32) : Spec.umulhiRel x y (Sem.umulhi x y) := umulhi_spec x y
theorem umulhi_i64 (x y : BitVec 64) : Spec.umulhiRel x y (Sem.umulhi x y) := umulhi_spec x y
theorem smulhi_i8 (x y : BitVec 8) : Spec.smulhiRel x y (Sem.smulhi x y) := smulhi_spec x y
theorem smulhi_i16 (x y : BitVec 16) : Spec.smulhiRel x y (Sem.smulhi x y) := smulhi_spec x y
theorem smulhi_i32 (x y : BitVec 32) : Spec.smulhiRel x y (Sem.smulhi x y) := smulhi_spec x y
theorem smulhi_i64 (x y : BitVec 64) : Spec.smulhiRel x y (Sem.smulhi x y) := smulhi_spec x y

theorem udiv_i8 (x y : BitVec 8) : toSpec (Sem.udiv x y) = Spec.udiv x y := udiv_eq x y
theorem udiv_i16 (x y : BitVec 16) : toSpec (Sem.udiv x y) = Spec.udiv x y := udiv_eq x y
theorem udiv_i32 (x y : BitVec 32) : toSpec (Sem.udiv x y) = Spec.udiv x y := udiv_eq x y
theorem udiv_i64 (x y : BitVec 64) : toSpec (Sem.udiv x y) = Spec.udiv x y := udiv_eq x y
theorem urem_i8 (x y : BitVec 8) : toSpec (Sem.urem x y) = Spec.urem x y := urem_eq x y
theorem urem_i16 (x y : BitVec 16) : toSpec (Sem.urem x y) = Spec.urem x y := urem_eq x y
theorem urem_i32 (x y : BitVec 32) : toSpec (Sem.urem x y) = Spec.urem x y := urem_eq x y
theorem urem_i64 (x y : BitVec 64) : toSpec (Sem.urem x y) = Spec.urem x y := urem_eq x y

-- `sdiv` at one width: split on the two trap conditions, then bit-blast the division.
set_option hygiene false in
macro "sdiv_tac" : tactic => `(tactic| (
  unfold Sem.sdiv Spec.sdiv
  by_cases h0 : y = 0
  · rw [ite_eq_left h0, ite_eq_left h0]; rfl
  · rw [ite_eq_right h0, ite_eq_right h0]
    by_cases h1 : x = BitVec.intMin _ ∧ y = BitVec.allOnes _
    · have h2 : x = bvTopBitSet _ ∧ bvIsZero (~~~y) := by
        obtain ⟨hx, hy⟩ := h1
        subst hx hy
        decide
      rw [ite_eq_left h1, ite_eq_left h2]; rfl
    · have h2 : ¬ (x = bvTopBitSet _ ∧ bvIsZero (~~~y)) := by
        intro ⟨hx, hy⟩
        apply h1
        exact ⟨by subst hx; decide, by unfold bvIsZero at hy; bv_decide⟩
      rw [ite_eq_right h1, ite_eq_right h2]
      show SpecOut.val _ = SpecOut.val _
      congr 1
      unfold bvsdiv bvudiv
      bv_decide))

theorem sdiv_i8 (x y : BitVec 8) : toSpec (Sem.sdiv x y) = Spec.sdiv x y := by sdiv_tac
theorem sdiv_i16 (x y : BitVec 16) : toSpec (Sem.sdiv x y) = Spec.sdiv x y := by sdiv_tac
theorem sdiv_i32 (x y : BitVec 32) : toSpec (Sem.sdiv x y) = Spec.sdiv x y := by sdiv_tac
theorem sdiv_i64 (x y : BitVec 64) : toSpec (Sem.sdiv x y) = Spec.sdiv x y := by sdiv_tac

set_option hygiene false in
macro "srem_tac" : tactic => `(tactic| (
  unfold Sem.srem Spec.srem
  by_cases h0 : y = 0
  · rw [ite_eq_left h0, ite_eq_left h0]; rfl
  · rw [ite_eq_right h0, ite_eq_right h0]
    show SpecOut.val _ = SpecOut.val _
    congr 1
    unfold bvsrem bvurem
    bv_decide))

theorem srem_i8 (x y : BitVec 8) : toSpec (Sem.srem x y) = Spec.srem x y := by srem_tac
theorem srem_i16 (x y : BitVec 16) : toSpec (Sem.srem x y) = Spec.srem x y := by srem_tac
theorem srem_i32 (x y : BitVec 32) : toSpec (Sem.srem x y) = Spec.srem x y := by srem_tac
theorem srem_i64 (x y : BitVec 64) : toSpec (Sem.srem x y) = Spec.srem x y := by srem_tac

/-! Shifts and rotates, for every operand width `2^k` (i8..i64) and every amount width
`v ≤ 64` (this covers all `bv_shift_8_to_64` and `bv_shift_8_to_64_extra` instantiations). -/

theorem ishl_i8 {v : Nat} (hv : v ≤ 64) (x : BitVec 8) (y : BitVec v) :
    Sem.ishl x y = Spec.ishl x y := ishl_eq 3 x y hv (by decide)
theorem ishl_i16 {v : Nat} (hv : v ≤ 64) (x : BitVec 16) (y : BitVec v) :
    Sem.ishl x y = Spec.ishl x y := ishl_eq 4 x y hv (by decide)
theorem ishl_i32 {v : Nat} (hv : v ≤ 64) (x : BitVec 32) (y : BitVec v) :
    Sem.ishl x y = Spec.ishl x y := ishl_eq 5 x y hv (by decide)
theorem ishl_i64 {v : Nat} (hv : v ≤ 64) (x : BitVec 64) (y : BitVec v) :
    Sem.ishl x y = Spec.ishl x y := ishl_eq 6 x y hv (by decide)
theorem ushr_i8 {v : Nat} (hv : v ≤ 64) (x : BitVec 8) (y : BitVec v) :
    Sem.ushr x y = Spec.ushr x y := ushr_eq 3 x y hv (by decide)
theorem ushr_i16 {v : Nat} (hv : v ≤ 64) (x : BitVec 16) (y : BitVec v) :
    Sem.ushr x y = Spec.ushr x y := ushr_eq 4 x y hv (by decide)
theorem ushr_i32 {v : Nat} (hv : v ≤ 64) (x : BitVec 32) (y : BitVec v) :
    Sem.ushr x y = Spec.ushr x y := ushr_eq 5 x y hv (by decide)
theorem ushr_i64 {v : Nat} (hv : v ≤ 64) (x : BitVec 64) (y : BitVec v) :
    Sem.ushr x y = Spec.ushr x y := ushr_eq 6 x y hv (by decide)
theorem sshr_i8 {v : Nat} (hv : v ≤ 64) (x : BitVec 8) (y : BitVec v) :
    Sem.sshr x y = Spec.sshr x y := sshr_eq 3 x y hv (by decide)
theorem sshr_i16 {v : Nat} (hv : v ≤ 64) (x : BitVec 16) (y : BitVec v) :
    Sem.sshr x y = Spec.sshr x y := sshr_eq 4 x y hv (by decide)
theorem sshr_i32 {v : Nat} (hv : v ≤ 64) (x : BitVec 32) (y : BitVec v) :
    Sem.sshr x y = Spec.sshr x y := sshr_eq 5 x y hv (by decide)
theorem sshr_i64 {v : Nat} (hv : v ≤ 64) (x : BitVec 64) (y : BitVec v) :
    Sem.sshr x y = Spec.sshr x y := sshr_eq 6 x y hv (by decide)
theorem rotl_i8 {v : Nat} (hv : v ≤ 64) (x : BitVec 8) (y : BitVec v) :
    Sem.rotl x y = Spec.rotl x y := rotl_eq 3 x y hv (by decide)
theorem rotl_i16 {v : Nat} (hv : v ≤ 64) (x : BitVec 16) (y : BitVec v) :
    Sem.rotl x y = Spec.rotl x y := rotl_eq 4 x y hv (by decide)
theorem rotl_i32 {v : Nat} (hv : v ≤ 64) (x : BitVec 32) (y : BitVec v) :
    Sem.rotl x y = Spec.rotl x y := rotl_eq 5 x y hv (by decide)
theorem rotl_i64 {v : Nat} (hv : v ≤ 64) (x : BitVec 64) (y : BitVec v) :
    Sem.rotl x y = Spec.rotl x y := rotl_eq 6 x y hv (by decide)
theorem rotr_i8 {v : Nat} (hv : v ≤ 64) (x : BitVec 8) (y : BitVec v) :
    Sem.rotr x y = Spec.rotr x y := rotr_eq 3 x y hv (by decide)
theorem rotr_i16 {v : Nat} (hv : v ≤ 64) (x : BitVec 16) (y : BitVec v) :
    Sem.rotr x y = Spec.rotr x y := rotr_eq 4 x y hv (by decide)
theorem rotr_i32 {v : Nat} (hv : v ≤ 64) (x : BitVec 32) (y : BitVec v) :
    Sem.rotr x y = Spec.rotr x y := rotr_eq 5 x y hv (by decide)
theorem rotr_i64 {v : Nat} (hv : v ≤ 64) (x : BitVec 64) (y : BitVec v) :
    Sem.rotr x y = Spec.rotr x y := rotr_eq 6 x y hv (by decide)

/-! `clz`: `(= result (clz x))` with the binary-search encoding. -/

theorem clz_i8 (x : BitVec 8) : Sem.clz x = Spec.clz x := by
  simp only [Sem.clz, Spec.clz, SpecCrossread.clz, clzShifts, clzRounds]; bv_decide
theorem clz_i16 (x : BitVec 16) : Sem.clz x = Spec.clz x := by
  simp only [Sem.clz, Spec.clz, SpecCrossread.clz, clzShifts, clzRounds]; bv_decide
theorem clz_i32 (x : BitVec 32) : Sem.clz x = Spec.clz x := by
  simp only [Sem.clz, Spec.clz, SpecCrossread.clz, clzShifts, clzRounds]; bv_decide
theorem clz_i64 (x : BitVec 64) : Sem.clz x = Spec.clz x := by
  simp only [Sem.clz, Spec.clz, SpecCrossread.clz, clzShifts, clzRounds]; bv_decide

/-! `ctz`: `(= result (clz (rev x)))`. -/

theorem ctz_i8 (x : BitVec 8) : Sem.ctz x = SpecCrossread.clz (rev8 x) := by
  simp only [Sem.ctz, SpecCrossread.clz, clzShifts, clzRounds, rev8, revRounds, List.foldl]
  bv_decide
theorem ctz_i16 (x : BitVec 16) : Sem.ctz x = SpecCrossread.clz (rev16 x) := by
  simp only [Sem.ctz, SpecCrossread.clz, clzShifts, clzRounds, rev16, revRounds, List.foldl]
  bv_decide
theorem ctz_i32 (x : BitVec 32) : Sem.ctz x = SpecCrossread.clz (rev32 x) := by
  simp only [Sem.ctz, SpecCrossread.clz, clzShifts, clzRounds, rev32, revRounds, List.foldl]
  bv_decide
theorem ctz_i64 (x : BitVec 64) : Sem.ctz x = SpecCrossread.clz (rev64 x) := by
  simp only [Sem.ctz, SpecCrossread.clz, clzShifts, clzRounds, rev64, revRounds, List.foldl]
  bv_decide

/-! `popcnt`: `(= result (popcnt x))`, bits summed in `log2 w + 1` bits. -/

theorem popcnt_i8 (x : BitVec 8) : Sem.popcnt x = popcnt 4 x := by
  simp only [Sem.popcnt, popcnt, popSum]; bv_decide
theorem popcnt_i16 (x : BitVec 16) : Sem.popcnt x = popcnt 5 x := by
  simp only [Sem.popcnt, popcnt, popSum]; bv_decide
theorem popcnt_i32 (x : BitVec 32) : Sem.popcnt x = popcnt 6 x := by
  simp only [Sem.popcnt, popcnt, popSum]; bv_decide
theorem popcnt_i64 (x : BitVec 64) : Sem.popcnt x = popcnt 7 x := by
  simp only [Sem.popcnt, popcnt, popSum]; bv_decide

theorem icmp_i8 (cc : IntCC) (x y : BitVec 8) : Sem.icmp cc x y = Spec.icmp cc x y :=
  icmp_eq cc x y
theorem icmp_i16 (cc : IntCC) (x y : BitVec 16) : Sem.icmp cc x y = Spec.icmp cc x y :=
  icmp_eq cc x y
theorem icmp_i32 (cc : IntCC) (x y : BitVec 32) : Sem.icmp cc x y = Spec.icmp cc x y :=
  icmp_eq cc x y
theorem icmp_i64 (cc : IntCC) (x y : BitVec 64) : Sem.icmp cc x y = Spec.icmp cc x y :=
  icmp_eq cc x y

/-! `uextend`/`sextend` for every instantiation of the `extend` form. -/

theorem uextend_8_16 (x : BitVec 8) : Sem.uextend 16 x = Spec.uextend 16 x := by
  unfold Sem.uextend Spec.uextend; bv_decide
theorem uextend_8_32 (x : BitVec 8) : Sem.uextend 32 x = Spec.uextend 32 x := by
  unfold Sem.uextend Spec.uextend; bv_decide
theorem uextend_8_64 (x : BitVec 8) : Sem.uextend 64 x = Spec.uextend 64 x := by
  unfold Sem.uextend Spec.uextend; bv_decide
theorem uextend_16_32 (x : BitVec 16) : Sem.uextend 32 x = Spec.uextend 32 x := by
  unfold Sem.uextend Spec.uextend; bv_decide
theorem uextend_16_64 (x : BitVec 16) : Sem.uextend 64 x = Spec.uextend 64 x := by
  unfold Sem.uextend Spec.uextend; bv_decide
theorem uextend_32_64 (x : BitVec 32) : Sem.uextend 64 x = Spec.uextend 64 x := by
  unfold Sem.uextend Spec.uextend; bv_decide
theorem sextend_8_16 (x : BitVec 8) : Sem.sextend 16 x = Spec.sextend 16 x := by
  unfold Sem.sextend Spec.sextend; bv_decide
theorem sextend_8_32 (x : BitVec 8) : Sem.sextend 32 x = Spec.sextend 32 x := by
  unfold Sem.sextend Spec.sextend; bv_decide
theorem sextend_8_64 (x : BitVec 8) : Sem.sextend 64 x = Spec.sextend 64 x := by
  unfold Sem.sextend Spec.sextend; bv_decide
theorem sextend_16_32 (x : BitVec 16) : Sem.sextend 32 x = Spec.sextend 32 x := by
  unfold Sem.sextend Spec.sextend; bv_decide
theorem sextend_16_64 (x : BitVec 16) : Sem.sextend 64 x = Spec.sextend 64 x := by
  unfold Sem.sextend Spec.sextend; bv_decide
theorem sextend_32_64 (x : BitVec 32) : Sem.sextend 64 x = Spec.sextend 64 x := by
  unfold Sem.sextend Spec.sextend; bv_decide

/-! `ireduce` for every instantiation. -/

theorem ireduce_16_8 (x : BitVec 16) : Sem.ireduce 8 x = Spec.ireduce 8 x := by
  unfold Sem.ireduce Spec.ireduce; bv_decide
theorem ireduce_32_8 (x : BitVec 32) : Sem.ireduce 8 x = Spec.ireduce 8 x := by
  unfold Sem.ireduce Spec.ireduce; bv_decide
theorem ireduce_64_8 (x : BitVec 64) : Sem.ireduce 8 x = Spec.ireduce 8 x := by
  unfold Sem.ireduce Spec.ireduce; bv_decide
theorem ireduce_32_16 (x : BitVec 32) : Sem.ireduce 16 x = Spec.ireduce 16 x := by
  unfold Sem.ireduce Spec.ireduce; bv_decide
theorem ireduce_64_16 (x : BitVec 64) : Sem.ireduce 16 x = Spec.ireduce 16 x := by
  unfold Sem.ireduce Spec.ireduce; bv_decide
theorem ireduce_64_32 (x : BitVec 64) : Sem.ireduce 32 x = Spec.ireduce 32 x := by
  unfold Sem.ireduce Spec.ireduce; bv_decide

theorem iconst_i8 (r : BitVec 8) : ∀ r', r.zeroExtend 64 = r'.zeroExtend 64 → r' = r :=
  iconst_spec r (by decide)
theorem iconst_i16 (r : BitVec 16) : ∀ r', r.zeroExtend 64 = r'.zeroExtend 64 → r' = r :=
  iconst_spec r (by decide)
theorem iconst_i32 (r : BitVec 32) : ∀ r', r.zeroExtend 64 = r'.zeroExtend 64 → r' = r :=
  iconst_spec r (by decide)
theorem iconst_i64 (r : BitVec 64) : ∀ r', r.zeroExtend 64 = r'.zeroExtend 64 → r' = r :=
  iconst_spec r (by decide)

/-! Loads read exactly what a store of the same size wrote (little-endian), which is the
spec's `loaded_value`/`clif_store` value correspondence; `istoreN` stores
`(extract (N-1) 0 value)`. -/

theorem store_load_1 (m : Mem) (a : Nat) (x : BitVec 8) :
    (m.writeBits false a 1 x).readBits false a 1 8 = some x := by
  simp [Mem.readBits, Mem.writeBits, Mem.byteIndex, List.range, List.range.loop,
    List.foldlM] <;> bv_decide
theorem store_load_2 (m : Mem) (a : Nat) (x : BitVec 16) :
    (m.writeBits false a 2 x).readBits false a 2 16 = some x := by
  simp [Mem.readBits, Mem.writeBits, Mem.byteIndex, List.range, List.range.loop,
    List.foldlM] <;> bv_decide
theorem store_load_4 (m : Mem) (a : Nat) (x : BitVec 32) :
    (m.writeBits false a 4 x).readBits false a 4 32 = some x := by
  simp [Mem.readBits, Mem.writeBits, Mem.byteIndex, List.range, List.range.loop,
    List.foldlM] <;> bv_decide
theorem store_load_8 (m : Mem) (a : Nat) (x : BitVec 64) :
    (m.writeBits false a 8 x).readBits false a 8 64 = some x := by
  simp [Mem.readBits, Mem.writeBits, Mem.byteIndex, List.range, List.range.loop,
    List.foldlM] <;> bv_decide
theorem istore8_bits (m : Mem) (a : Nat) (x : BitVec 64) :
    (m.writeBits false a 1 x).readBits false a 1 8 = some (x.extractLsb' 0 8) := by
  simp [Mem.readBits, Mem.writeBits, Mem.byteIndex, List.range, List.range.loop,
    List.foldlM] <;> bv_decide
theorem istore16_bits (m : Mem) (a : Nat) (x : BitVec 64) :
    (m.writeBits false a 2 x).readBits false a 2 16 = some (x.extractLsb' 0 16) := by
  simp [Mem.readBits, Mem.writeBits, Mem.byteIndex, List.range, List.range.loop,
    List.foldlM] <;> bv_decide
theorem istore32_bits (m : Mem) (a : Nat) (x : BitVec 64) :
    (m.writeBits false a 4 x).readBits false a 4 32 = some (x.extractLsb' 0 32) := by
  simp [Mem.readBits, Mem.writeBits, Mem.byteIndex, List.range, List.range.loop,
    List.foldlM] <;> bv_decide

/-! ### Non-E opcodes with a spec -/

theorem iabs_i8 (x : BitVec 8) : Sem.iabs x = Spec.iabs x := iabs_eq x
theorem iabs_i16 (x : BitVec 16) : Sem.iabs x = Spec.iabs x := iabs_eq x
theorem iabs_i32 (x : BitVec 32) : Sem.iabs x = Spec.iabs x := iabs_eq x
theorem iabs_i64 (x : BitVec 64) : Sem.iabs x = Spec.iabs x := iabs_eq x

theorem uaddOverflowTrap_i32 (x y : BitVec 32) (c : TrapCode) :
    toSpec (Sem.uaddOverflowTrap x y c) = Spec.uaddOverflowTrap x y := by
  have hc : BitVec.uaddOverflow x y = (x.zeroExtend 65 + y.zeroExtend 65).getLsbD 32 := by
    bv_decide
  have hs : (x.zeroExtend 65 + y.zeroExtend 65).setWidth 32 = x + y := by bv_decide
  unfold Sem.uaddOverflowTrap Spec.uaddOverflowTrap
  simp only [hc, hs]
  split <;> rfl
theorem uaddOverflowTrap_i64 (x y : BitVec 64) (c : TrapCode) :
    toSpec (Sem.uaddOverflowTrap x y c) = Spec.uaddOverflowTrap x y := by
  have hc : BitVec.uaddOverflow x y = (x.zeroExtend 65 + y.zeroExtend 65).getLsbD 64 := by
    bv_decide
  have hs : (x.zeroExtend 65 + y.zeroExtend 65).setWidth 64 = x + y := by bv_decide
  unfold Sem.uaddOverflowTrap Spec.uaddOverflowTrap
  simp only [hc, hs]
  split <;> rfl

end PerWidth

end Clif.SpecCrossread
