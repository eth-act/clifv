import FV.Clif.Mem

/-!
# `Opt.MidVal`: the memory facts behind redundant-load elimination and store-to-load forwarding

The validator `Opt.MidVal.check` (#1119) lets cg_clif's optimised function drop a load of the
unoptimised one when the loaded location is known: an access of the same address, size and byte
order happened earlier at the same memory version (no write, call or free in between), so the
memory is the one that access left. These are the facts about `Clif.Mem` that make that sound,
in either byte order:

* `Mem.load_of_store`: a load of the bytes a store just wrote reads the stored value
  (store-to-load forwarding);
* `Mem.load_of_load`: a second load of the same bytes reads what the first one read (redundant
  load elimination).

In both, the second access **cannot trap**: the first one succeeded, so the bytes lie in one
live allocation and are initialised, and the memory is unchanged. The only other outcome is
`stuck` (an `aligned` flag on a misaligned address), on which the refinement the passes prove
(`Opt.OutcomeRefines`) claims nothing. This is the answer to "a removed load cannot trap in g
where it would in f" in the design (#1119 issuecomment-7009592817): it never would have.
-/

namespace Clif.Mem

/-! ## Byte order -/

theorem byteIndex_lt {big : Bool} {n i : Nat} (h : i < n) : byteIndex big n i < n := by
  unfold byteIndex; split <;> omega

theorem byteIndex_byteIndex {big : Bool} {n i : Nat} (h : i < n) :
    byteIndex big n (byteIndex big n i) = i := by
  unfold byteIndex; split <;> omega

/-! ## Reading bytes in either order -/

/-- One step of `readBits`. -/
def readStep (m : Mem) (big : Bool) (addr n w : Nat) (acc : BitVec w) (i : Nat) :
    Option (BitVec w) := do
  let b ← m.bytes (addr + byteIndex big n i)
  pure (acc ||| (b.zeroExtend w <<< (8 * i)))

theorem readBits_eq (m : Mem) (big : Bool) (addr n w : Nat) :
    m.readBits big addr n w = (List.range n).foldlM (readStep m big addr n w) 0 := rfl

/-- The bits the first `k` steps of `readBits` assemble: byte `byteIndex (j / 8)`, bit
`j % 8`, below `8 k` (and `w`). -/
theorem readFold_spec {m : Mem} {big : Bool} {addr n w : Nat} :
    ∀ k x, (List.range k).foldlM (readStep m big addr n w) 0 = some x →
      (∀ i < k, (m.bytes (addr + byteIndex big n i)).isSome) ∧
      ∀ j, x.getLsbD j = (decide (j < w) && decide (j < 8 * k) &&
        ((m.bytes (addr + byteIndex big n (j / 8))).getD 0).getLsbD (j % 8)) := by
  intro k
  induction k with
  | zero =>
    intro x h
    simp only [List.range_zero, List.foldlM_nil] at h
    cases h
    exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun j => by simp⟩
  | succ k ih =>
    intro x h
    rw [List.range_succ, List.foldlM_append] at h
    obtain ⟨acc, hacc, h2⟩ := Option.bind_eq_some_iff.1 h
    simp only [List.foldlM_cons, List.foldlM_nil, readStep] at h2
    obtain ⟨b, hb, h3⟩ := Option.bind_eq_some_iff.1 h2
    simp only [Option.bind_some, pure] at h3
    cases h3
    obtain ⟨h1, hs⟩ := ih acc hacc
    refine ⟨fun i hi => ?_, fun j => ?_⟩
    · by_cases hik : i < k
      · exact h1 i hik
      · rw [show i = k by omega, hb]; rfl
    · rw [BitVec.getLsbD_or, hs, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zeroExtend]
      by_cases hj : j < 8 * k
      · have hj2 : j < 8 * (k + 1) := by omega
        simp only [hj, hj2, decide_true, Bool.and_true, Bool.not_true, Bool.and_false,
          Bool.false_and, Bool.or_false]
      · by_cases hj3 : j < 8 * (k + 1)
        · have e1 : j / 8 = k := by omega
          have e2 : j - 8 * k = j % 8 := by omega
          simp only [hj, hj3, decide_false, decide_true, Bool.and_false, Bool.false_or,
            Bool.not_false, Bool.and_true, e1, e2, hb, Option.getD_some]
          by_cases hjw : j < w
          · have : j % 8 < w := Nat.lt_of_le_of_lt (Nat.mod_le j 8) hjw
            simp [hjw, this]
          · simp [hjw]
        · simp only [hj, hj3, decide_false, Bool.and_false, Bool.false_or, Bool.not_false,
            Bool.and_true]
          rw [BitVec.getLsbD_of_ge b _ (by omega)]
          simp

/-- `readBits` succeeds when every byte it reads is initialised. -/
theorem readFold_some {m : Mem} {big : Bool} {addr n w : Nat} :
    ∀ k, (∀ i < k, (m.bytes (addr + byteIndex big n i)).isSome) →
      ∃ x, (List.range k).foldlM (readStep m big addr n w) 0 = some x := by
  intro k
  induction k with
  | zero => intro _; exact ⟨0, rfl⟩
  | succ k ih =>
    intro h
    obtain ⟨acc, hacc⟩ := ih fun i hi => h i (by omega)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h k (by omega))
    rw [List.range_succ, List.foldlM_append, hacc]
    exact ⟨acc ||| (b.zeroExtend w <<< (8 * k)), by simp [readStep, hb, pure]⟩

/-! ## A read of what was written -/

/-- The byte `writeBits` puts at `addr + byteIndex big n i`: byte `i` of the value. -/
theorem writeBits_bytes {m : Mem} {big : Bool} {addr n i w : Nat} {x : BitVec w} (hi : i < n) :
    (m.writeBits big addr n x).bytes (addr + byteIndex big n i) = some (x.extractLsb' (8 * i) 8) := by
  have hb := byteIndex_lt (big := big) hi
  simp only [writeBits, show addr ≤ addr + byteIndex big n i by omega,
    show addr + byteIndex big n i < addr + n by omega, and_self, if_true,
    Nat.add_sub_cancel_left, byteIndex_byteIndex hi]

/-- **Reading back a write**: the `n` bytes just written at `addr`, read in the same byte order
as `8 n` bits, are the low `8 n` bits of the written value. -/
theorem readBits_writeBits (m : Mem) (big : Bool) (addr n : Nat) {w : Nat} (x : BitVec w) :
    (m.writeBits big addr n x).readBits big addr n (8 * n) = some (x.setWidth (8 * n)) := by
  obtain ⟨y, hy⟩ := readFold_some (m := m.writeBits big addr n x) (big := big) (addr := addr)
    (n := n) (w := 8 * n) n fun i hi => by rw [writeBits_bytes hi]; rfl
  rw [readBits_eq, hy]
  congr 1
  obtain ⟨-, hs⟩ := readFold_spec n y hy
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [hs, BitVec.getLsbD_setWidth]
  have hj8 : j / 8 < n := by omega
  rw [writeBits_bytes hj8, Option.getD_some, BitVec.getLsbD_extractLsb']
  simp only [hj, decide_true, Bool.true_and, Nat.mod_lt j (by omega : 0 < 8)]
  rw [show 8 * (j / 8) + j % 8 = j by omega]

/-! ## Validity is kept by a write -/

@[simp] theorem writeBits_allocs (m : Mem) (big : Bool) (addr n : Nat) {w : Nat} (x : BitVec w) :
    (m.writeBits big addr n x).allocs = m.allocs := rfl

@[simp] theorem writeBits_valid (m : Mem) (big : Bool) (addr n : Nat) {w : Nat} (x : BitVec w)
    (a k : Nat) : (m.writeBits big addr n x).valid a k = m.valid a k := rfl

theorem checkAccess_ok_valid {m : Mem} {fl : MemFlags} {a n : Nat}
    (h : m.checkAccess fl a n = .ok ()) : m.valid a n = true := by
  unfold checkAccess at h
  split at h
  · assumption
  · split at h <;> cases h

/-- On a valid range an access check succeeds or is `stuck` (never traps). -/
theorem checkAccess_of_valid {m : Mem} (fl : MemFlags) {a n : Nat} (h : m.valid a n = true) :
    m.checkAccess fl a n = .ok () ∨ ∃ msg, m.checkAccess fl a n = .stuck msg := by
  unfold checkAccess
  simp only [h, if_true]
  split
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

/-! ## The two forwarding facts -/

/-- **Store-to-load forwarding.** After a store of `x` (`n` bytes at `a`, byte order of `fl`)
succeeded, a load of the same `n` bytes in the same byte order (any other flags) reads the low
`8 n` bits of `x`, or is `stuck` (its `aligned` flag); it never traps. -/
theorem load_of_store {m m' : Mem} {fl fl' : MemFlags} {a n w : Nat} {x : BitVec w}
    (hs : m.store fl a n x = .ok m') (he : fl'.endianness = fl.endianness) :
    m'.load fl' a n (8 * n) = .ok (x.setWidth (8 * n)) ∨ ∃ msg, m'.load fl' a n (8 * n) = .stuck msg := by
  simp only [store] at hs
  cases hc : m.checkAccess fl a n with
  | trap c => rw [hc] at hs; cases hs
  | stuck msg => rw [hc] at hs; cases hs
  | ok u =>
    rw [hc] at hs
    have hv := checkAccess_ok_valid hc
    simp only [Res.ok_bind] at hs
    cases hro : (!m.readonlyAt a n) with
    | false => rw [hro] at hs; simp [Res.check] at hs; cases hs
    | true =>
      rw [hro] at hs
      simp only [Res.check_true, Res.ok_bind, Res.pure_eq] at hs
      cases hs
      simp only [load]
      rcases checkAccess_of_valid fl' (m := m.writeBits _ a n x) (by rw [writeBits_valid]; exact hv)
        with h | ⟨msg, h⟩
      · rw [h, he]
        simp only [Res.ok_bind, readBits_writeBits, Res.ofOption_some]
        exact Or.inl rfl
      · rw [h]; exact Or.inr ⟨msg, rfl⟩

/-- **Redundant-load elimination.** After a load of `n` bytes at `a` read `v`, a load of the same
bytes in the same byte order and width (any other flags) from the same memory reads `v`, or is
`stuck` (its `aligned` flag); it never traps. -/
theorem load_of_load {m : Mem} {fl fl' : MemFlags} {a n w : Nat} {v : BitVec w}
    (hl : m.load fl a n w = .ok v) (he : fl'.endianness = fl.endianness) :
    m.load fl' a n w = .ok v ∨ ∃ msg, m.load fl' a n w = .stuck msg := by
  simp only [load] at hl ⊢
  cases hc : m.checkAccess fl a n with
  | trap c => rw [hc] at hl; cases hl
  | stuck msg => rw [hc] at hl; cases hl
  | ok u =>
    rw [hc] at hl
    simp only [Res.ok_bind] at hl
    rcases checkAccess_of_valid fl' (checkAccess_ok_valid hc) with h | ⟨msg, h⟩
    · rw [h, he]
      simp only [Res.ok_bind]
      exact Or.inl hl
    · rw [h]; exact Or.inr ⟨msg, rfl⟩

end Clif.Mem
