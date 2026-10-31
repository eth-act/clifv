import FV.Opt.Proof.KernelBV

/-!
# Shift amounts and comparisons for `kbv`: `kbv_amt`, `kbv_cmp`

Bit-vector goals of `shifts.isle` and `spaceship.isle` rules that the general `kbv` search does not
close, decided by targeted kernel-checked rewriting (no SAT certificates, no `Lean.ofReduceBool`):

* `kbv_amt`: every shift by a bit-vector amount (also CLIF's `ishl`/`ushr`/`sshr`) becomes a shift
  by its `toNat` (`BitVec.shiftLeft_eq'`, …); two shifts in one direction become one shift by the
  sum (`BitVec.shiftLeft_add`, `ushiftRight_ushiftRight`, `BitVec.sshiftRight_add`); the amounts
  (masks `x &&& (2^k - 1)`, extensions, sums and differences) become `Nat` arithmetic over the
  operands' `toNat`s; then rotations written with two shifts become `rotateLeft` (`rotl_of`,
  `rotl_of'`, `rotateLeft_rotateLeft'`, `rotateLeft_of_mod_eq_zero`), a shift right then left, or
  left then right, becomes a mask (`shr_shl_of`, `sshr_shl_of`, `shl_shr_of`), an arithmetic shift
  right undoes a shift left of an extension that keeps the sign (`sshr_shl_setWidth`,
  `sshr_shl_signExtend`) or sign-extends a zero extension shifted to the top bit
  (`sshr_shl_setWidth_top`), the negated sign bit is the sign mask (`neg_ushiftRight_pred`), a mask
  moves across a shift left then right (`and_shl_shr_of`), two shifts left by one amount are
  collected (`shl_or_shl_of`), so are two shifts by one amount under an exclusive or
  (`shl_xor_shl_of`, `ushr_xor_ushr_of`, `sshr_xor_sshr_of`), all ones stay all ones under an
  arithmetic shift right (`allOnes_sshiftRight`), and the remaining shifts are compared by their
  amounts (`congr`, `omega`). The amount conditions of these lemmas are discharged by `omega`.
* `kbv_cmp`: comparisons (`slt`, `ult`, …) as `decide`s on `toInt`/`toNat`, every `if` split, each
  case closed by evaluation or `omega`. Both use only explicit `simp only` sets, so the `@[simp]`
  lemmas of the importing module do not change them.

A rule module opts in by a `local elab_rules` for `kbv` that runs one of them under `kbv_guard`
through `Opt.Proof.KernelBV.isolate` before the general search (to which a failure falls through).
-/

namespace Opt.Proof.ShiftAmt

/-- A rotation by a multiple of the width is the identity. -/
theorem rotateLeft_of_mod_eq_zero {w : Nat} (x : BitVec w) {k : Nat} (h : k % w = 0) :
    x.rotateLeft k = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_rotateLeft, h]
  simp [hi]

example : (0x81#8).rotateLeft 16 = 0x81#8 := rotateLeft_of_mod_eq_zero _ (by decide)

/-- A rotation left written with `Nat` shifts: `k + m = w` (also `k = w`, `m = 0` and
`k = 0`, `m = w`), or both amounts zero. -/
theorem rotl_of {w : Nat} (x : BitVec w) {k m : Nat} (h : k + m = w ∨ (k = 0 ∧ m = 0)) :
    x <<< k ||| x >>> m = x.rotateLeft (k % w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight]
  have hw : 0 < w := by omega
  rcases h with h | ⟨rfl, rfl⟩
  · by_cases hk : k < w
    · have hkw : k % w = k := Nat.mod_eq_of_lt hk
      simp only [hkw]
      by_cases h1 : i < k
      · have : m + i = w - k + i := by omega
        simp [h1, hi, this]
      · simp [h1, hi, BitVec.getLsbD_of_ge x (m + i) (by omega)]
    · have hk' : k = w := by omega
      have hm : m = 0 := by omega
      subst hk' hm
      simp [hi]
  · simp [hi]

example : 0x81#8 <<< 3 ||| 0x81#8 >>> 5 = (0x81#8).rotateLeft 3 := rotl_of _ (by decide)

/-- `rotl_of` with the operands of `|||` swapped (a rotation right by `m`). -/
theorem rotl_of' {w : Nat} (x : BitVec w) {k m : Nat} (h : k + m = w ∨ (k = 0 ∧ m = 0)) :
    x >>> m ||| x <<< k = x.rotateLeft (k % w) := by
  rw [BitVec.or_comm, rotl_of x h]

example : 0x81#8 >>> 0 ||| 0x81#8 <<< 8 = (0x81#8).rotateLeft 0 := rotl_of' _ (by decide)

/-- Rotations compose by adding their amounts. -/
theorem rotateLeft_rotateLeft' {w : Nat} (x : BitVec w) (a b : Nat) :
    (x.rotateLeft a).rotateLeft b = x.rotateLeft (a + b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hw : 0 < w := by omega
  have ha := Nat.mod_lt a hw
  have hb := Nat.mod_lt b hw
  have hab := Nat.mod_lt (a + b) hw
  have hs : (a + b) % w = (a % w + b % w) % w := Nat.add_mod a b w
  have hite : ∀ (p : Prop) [Decidable p] (q : Bool), (decide p && q) = if p then q else false := by
    intro p _ q; by_cases hp : p <;> simp [hp]
  have hs' : ((a + b) % w = a % w + b % w ∧ a % w + b % w < w) ∨
      ((a + b) % w + w = a % w + b % w) := by
    rw [hs]
    by_cases hlt : a % w + b % w < w
    · exact Or.inl ⟨Nat.mod_eq_of_lt hlt, hlt⟩
    · right; rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  simp only [BitVec.getLsbD_rotateLeft, hite]
  clear hite hs
  generalize a % w = a' at *
  generalize b % w = b' at *
  generalize (a + b) % w = s at *
  repeat' split
  all_goals first
    | rfl
    | (congr 1; omega)
    | (exfalso; omega)
    | (symm; apply BitVec.getLsbD_of_ge; omega)
    | (apply BitVec.getLsbD_of_ge; omega)

example : ((0x81#8).rotateLeft 3).rotateLeft 5 = (0x81#8).rotateLeft 8 := rotateLeft_rotateLeft' _ 3 5

/-- Clearing the low `a` bits by shifting right then left (amounts equal up to `hb`). -/
theorem shr_shl_of {w : Nat} (x : BitVec w) {a b : Nat} (hb : b = a) :
    x >>> a <<< b = x &&& BitVec.allOnes w <<< a := by
  subst hb; exact BitVec.shiftLeft_ushiftRight

example : 0x81#8 >>> 3 <<< 3 = 0x81#8 &&& BitVec.allOnes 8 <<< 3 := shr_shl_of _ rfl

/-- Clearing the high `a` bits by shifting left then right (amounts equal up to `hb`). -/
theorem shl_shr_of {w : Nat} (x : BitVec w) {a b : Nat} (hb : b = a) :
    x <<< a >>> b = x &&& BitVec.allOnes w >>> a := by
  subst hb
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and,
    BitVec.getLsbD_allOnes]
  by_cases h : b + i < w
  · simp [h, show ¬ b + i < b by omega, show b + i - b = i by omega, show i < w by omega]
  · simp [h]

example : 0x81#8 <<< 3 >>> 3 = 0x81#8 &&& BitVec.allOnes 8 >>> 3 := shl_shr_of _ rfl

/-- A mask shifted left then right by the same amount (`b = a`) moves to the other operand. -/
theorem and_shl_shr_of {w : Nat} (x y : BitVec w) {a b : Nat} (hb : b = a) :
    (y &&& x <<< a) >>> b = x &&& y >>> a := by
  subst hb
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and]
  by_cases h : b + i < w
  · simp [h, show ¬ b + i < b by omega, show b + i - b = i by omega, show i < w by omega,
      Bool.and_comm]
  · simp [h, BitVec.getLsbD_of_ge y (b + i) (by omega)]

example : (0x0F#8 &&& 0x81#8 <<< 3) >>> 3 = 0x81#8 &&& 0x0F#8 >>> 3 := and_shl_shr_of _ _ rfl

/-- Two shifts left by the same amount (`b = a`) of a disjunction's operands. -/
theorem shl_or_shl_of {w : Nat} (x y : BitVec w) {a b : Nat} (hb : b = a) :
    x <<< a ||| y <<< b = (x ||| y) <<< a := by
  subst hb; exact (BitVec.shiftLeft_or_distrib ..).symm

example : 0x81#8 <<< 3 ||| 0x12#8 <<< 3 = (0x81#8 ||| 0x12#8) <<< 3 := shl_or_shl_of _ _ rfl

/-- Two shifts by the same amount (`b = a`) of an exclusive or's operands (`arithmetic.isle`:
`bxor` of two `ishl`/`ushr`/`sshr` by one amount). -/
theorem shl_xor_shl_of {w : Nat} (x y : BitVec w) {a b : Nat} (hb : b = a) :
    x <<< a ^^^ y <<< b = (x ^^^ y) <<< a := by
  subst hb; exact (BitVec.shiftLeft_xor_distrib ..).symm

theorem ushr_xor_ushr_of {w : Nat} (x y : BitVec w) {a b : Nat} (hb : b = a) :
    x >>> a ^^^ y >>> b = (x ^^^ y) >>> a := by
  subst hb; exact (BitVec.ushiftRight_xor_distrib ..).symm

theorem sshr_xor_sshr_of {w : Nat} (x y : BitVec w) {a b : Nat} (hb : b = a) :
    x.sshiftRight a ^^^ y.sshiftRight b = (x ^^^ y).sshiftRight a := by
  subst hb; exact (BitVec.sshiftRight_xor_distrib ..).symm

example : 0x81#8 <<< 3 ^^^ 0x12#8 <<< 3 = (0x81#8 ^^^ 0x12#8) <<< 3 := shl_xor_shl_of _ _ rfl
example : 0x81#8 >>> 3 ^^^ 0x12#8 >>> 3 = (0x81#8 ^^^ 0x12#8) >>> 3 := ushr_xor_ushr_of _ _ rfl
example : (0x81#8).sshiftRight 3 ^^^ (0x12#8).sshiftRight 3 = (0x81#8 ^^^ 0x12#8).sshiftRight 3 :=
  sshr_xor_sshr_of _ _ rfl

/-- An arithmetic shift right of all ones is all ones. -/
theorem allOnes_sshiftRight {w : Nat} (n : Nat) :
    (BitVec.allOnes w).sshiftRight n = BitVec.allOnes w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_allOnes,
    BitVec.msb_allOnes (show 0 < w by omega)]
  by_cases h : n + i < w <;> simp [h, hi]

example : (BitVec.allOnes 8).sshiftRight 3 = BitVec.allOnes 8 := allOnes_sshiftRight 3

/-- Two logical shifts right add their amounts (`BitVec.shiftLeft_add` for `>>>`). -/
theorem ushiftRight_ushiftRight {w : Nat} (x : BitVec w) (n m : Nat) :
    x >>> n >>> m = x >>> (n + m) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_add]

example : 0x81#8 >>> 3 >>> 2 = 0x81#8 >>> 5 := ushiftRight_ushiftRight _ 3 2

/-- `shr_shl_of` with an arithmetic shift right. -/
theorem sshr_shl_of {w : Nat} (x : BitVec w) {a b : Nat} (hb : b = a) :
    x.sshiftRight a <<< b = x &&& BitVec.allOnes w <<< a := by
  rw [hb]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_sshiftRight]
  by_cases h : i < a
  · simp [h]
  · have h1 : ¬ w ≤ i - a := by omega
    have h3 : a + (i - a) = i := by omega
    simp [h, hi, h1, h3]
    intro _; omega

example : (0x81#8).sshiftRight 3 <<< 3 = 0x81#8 &&& BitVec.allOnes 8 <<< 3 := sshr_shl_of _ rfl

/-- An arithmetic shift right undoes a shift left of a zero extension that keeps the sign bit
clear (`v + k < w`). -/
theorem sshr_shl_setWidth {v w : Nat} (x : BitVec v) {k j : Nat} (hj : j = k) (h : v + k < w) :
    ((x.setWidth w) <<< k).sshiftRight j = x.setWidth w := by
  subst hj
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hmsb : ((x.setWidth w) <<< j).msb = false := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    by_cases hx : w - 1 - j < v
    · omega
    · simp
      intro _ _ _; exact BitVec.getLsbD_of_ge x _ (by omega)
  rw [BitVec.getLsbD_sshiftRight, hmsb]
  by_cases h1 : j + i < w
  · have h2 : ¬ w ≤ i := by omega
    have h3 : ¬ j + i < j := by omega
    simp [hi, h1, h2, h3]
  · simp [hi, h1]
    exact BitVec.getLsbD_of_ge x i (by omega)

example : (((0x81#8).setWidth 16) <<< 7).sshiftRight 7 = (0x81#8).setWidth 16 :=
  sshr_shl_setWidth _ rfl (by decide)

/-- An arithmetic shift right undoes a shift left of a sign extension that keeps the sign
(`v + k ≤ w`). -/
theorem sshr_shl_signExtend {v w : Nat} (x : BitVec v) {k j : Nat} (hj : j = k) (hv : 0 < v)
    (h : v + k ≤ w) : ((x.signExtend w) <<< k).sshiftRight j = x.signExtend w := by
  subst hj
  have hmsb : ((x.signExtend w) <<< j).msb = x.msb := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend]
    by_cases hx : w - 1 - j < v
    · have : w - 1 - j = v - 1 := by omega
      simp [this, show w - 1 < w by omega, show ¬ w - 1 < j by omega, show v - 1 < w by omega,
        BitVec.msb_eq_getLsbD_last]
    · simp [hx, show w - 1 < w by omega, show ¬ w - 1 < j by omega, show w - 1 - j < w by omega]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight, hmsb]
  by_cases h1 : j + i < w
  · have h2 : ¬ w ≤ i := by omega
    have h3 : ¬ j + i < j := by omega
    simp [hi, h1, h2, h3]
  · have : ¬ i < v := by omega
    rw [BitVec.getLsbD_signExtend]
    simp [hi, h1, this]

example : (((0x81#8).signExtend 16) <<< 8).sshiftRight 8 = (0x81#8).signExtend 16 :=
  sshr_shl_signExtend _ rfl (by decide) (by decide)

/-- An arithmetic shift right of a zero extension shifted to the top bit (`v + k = w`) is the
sign extension (`shifts.isle:50`: `sshr (ishl (uextend x) k) k` with `k = wide - narrow`). -/
theorem sshr_shl_setWidth_top {v w : Nat} (x : BitVec v) {k j : Nat} (hj : j = k) (h : v + k = w) :
    ((x.setWidth w) <<< k).sshiftRight j = x.signExtend w := by
  subst hj
  obtain rfl | hv := Nat.eq_zero_or_pos v
  · rw [BitVec.of_length_zero (x := x)]
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp [BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_signExtend]
  by_cases h1 : j + i < w
  · have h2 : ¬ w ≤ i := by omega
    have h3 : ¬ j + i < j := by omega
    have h4 : i < v := by omega
    simp [hi, h1, h2, h3, h4, show j + i - j = i by omega]
  · have h4 : ¬ i < v := by omega
    simp [hi, h1, h4, BitVec.msb_eq_getLsbD_last, show w - 1 < w by omega,
      show ¬ w - 1 < j by omega, show w - 1 - j = v - 1 by omega, show v - 1 < w by omega]

example : (((0x81#8).setWidth 16) <<< 8).sshiftRight 8 = (0x81#8).signExtend 16 :=
  sshr_shl_setWidth_top _ rfl (by decide)

/-- The negated sign bit (`x >>> (w - 1)`) is the sign mask (`x.sshiftRight (w - 1)`). -/
theorem neg_ushiftRight_pred {w n : Nat} (h : n + 1 = w) (x : BitVec w) :
    -(x >>> n) = x.sshiftRight n := by
  rw [Opt.Proof.KernelBV.ushiftRight_pred_width h, Opt.Proof.KernelBV.sshiftRight_pred_width h]
  cases x.msb <;> simp [BitVec.neg_one_eq_allOnes]

example : -((0x81#8) >>> 7) = (0x81#8).sshiftRight 7 := neg_ushiftRight_pred (by decide) _

end Opt.Proof.ShiftAmt

/-- Close an equation of shifts by equal amounts: `rfl`, `omega`, or congruence (three levels:
`x <<< a ||| x >>> b`, the shifts, their amounts). -/
macro "amt_congr" : tactic => `(tactic| first | rfl | omega |
  (congr 1 <;> first | rfl | omega | (congr 1 <;> first | rfl | omega | (congr 1 <;> first | rfl | omega))))

/-- Shift-amount goals (see the module docstring). -/
macro "kbv_amt" : tactic => `(tactic| (
  intros
  (try simp only [Option.some.injEq, Clif.Sem.ishl, Clif.Sem.ushr, Clif.Sem.sshr] at *)
  (try subst_vars)
  (try simp (disch := decide) only [Opt.Proof.KernelBV.setWidth_eq_iff_toNat, BitVec.toNat_inj] at *)
  (try subst_vars)
  (try simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.sshiftRight_eq', BitVec.lt_def,
    BitVec.le_def] at *)
  (try simp only [← BitVec.shiftLeft_add, Opt.Proof.ShiftAmt.ushiftRight_ushiftRight,
    ← BitVec.sshiftRight_add] at *)
  (try simp (disch := decide) only [Opt.Proof.KernelBV.reduceToNatAndMask, Opt.Proof.KernelBV.toNat_signExtend_mod,
    Opt.Proof.KernelBV.toNat_setWidth_mod, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_setWidth, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub] at *)
  (try simp (disch := decide) only [Opt.Proof.KernelBV.reduceToNatAndMask, Opt.Proof.KernelBV.toNat_signExtend_mod,
    Opt.Proof.KernelBV.toNat_setWidth_mod, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_setWidth, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub] at *)
  (try simp (disch := omega) only [Opt.Proof.ShiftAmt.rotl_of, Opt.Proof.ShiftAmt.rotl_of',
    Opt.Proof.ShiftAmt.shr_shl_of, Opt.Proof.ShiftAmt.shl_shr_of, Opt.Proof.ShiftAmt.sshr_shl_of,
    Opt.Proof.ShiftAmt.sshr_shl_setWidth,
    Opt.Proof.ShiftAmt.sshr_shl_signExtend, Opt.Proof.ShiftAmt.sshr_shl_setWidth_top,
    Opt.Proof.ShiftAmt.neg_ushiftRight_pred, Opt.Proof.ShiftAmt.and_shl_shr_of,
    Opt.Proof.ShiftAmt.shl_or_shl_of, Opt.Proof.ShiftAmt.shl_xor_shl_of,
    Opt.Proof.ShiftAmt.ushr_xor_ushr_of, Opt.Proof.ShiftAmt.sshr_xor_sshr_of,
    Opt.Proof.ShiftAmt.allOnes_sshiftRight])
  (try simp only [Opt.Proof.ShiftAmt.rotateLeft_rotateLeft'])
  (try simp (disch := omega) only [Opt.Proof.ShiftAmt.rotateLeft_of_mod_eq_zero])
  all_goals amt_congr))

/-- Goals over comparison results (see the module docstring). -/
macro "kbv_cmp" : tactic => `(tactic| (
  intros
  simp only [BitVec.slt, BitVec.sle, BitVec.ult, BitVec.ule, Bool.cond_eq_ite, beq_iff_eq,
    Bool.not_eq_true', Bool.not_eq_eq_eq_not, Bool.not_true]
  repeat' split
  all_goals first | rfl | decide | ((try simp (config := {decide := true}) only [decide_eq_true_eq,
    decide_eq_false_iff_not, Bool.not_eq_true, beq_iff_eq] at *) <;> omega)))

