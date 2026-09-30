import FV.Opt.Proof.LegalStep

/-!
# Memory lemmas of the split `i128` access

`Opt.Legalize128` rewrites a 16-byte little-endian load/store at address `A` into two 8-byte
accesses at `A` and `A + 8`. When the 16-byte access succeeds, so do the two halves, with the
low/high halves of the value (`load_split`, `store_split`): the range `[A, A + 16)` lies in one
allocation, so both halves do (`valid_sub`), an `aligned` 16-byte access is 8-aligned, and the
bytes are the same (`readBits_spec`, `writeBits_split`). The second address is `A + 8` without
wrap-around when every valid range lies below `2^64` (`MemBounded`, `effAddr_add8`).
-/

namespace Opt.Legal

open Clif

/-- Every valid range of `m` lies below `2^64` (the machine's address space). -/
def MemBounded (m : Mem) : Prop := ∀ a n, m.valid a n = true → a + n ≤ 2 ^ 64

theorem valid_sub {m : Mem} {a n b k : Nat} (h : m.valid a n = true) (h1 : a ≤ b)
    (h2 : b + k ≤ a + n) : m.valid b k = true := by
  simp only [Mem.valid, List.any_eq_true, Alloc.contains, Bool.and_eq_true,
    decide_eq_true_eq] at h ⊢
  obtain ⟨al, hal, h3, h4⟩ := h
  exact ⟨al, hal, by omega, by omega⟩

theorem readonlyAt_sub {m : Mem} {a n b k : Nat} (h : m.readonlyAt b k = true) (h1 : a ≤ b)
    (h2 : b + k ≤ a + n) : m.readonlyAt a n = true := by
  simp only [Mem.readonlyAt, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨al, hal, ⟨h3, h4⟩, h5⟩ := h
  exact ⟨al, hal, ⟨h3, by omega⟩, by omega⟩

/-! ## Reading bytes -/

theorem readBits_succ (m : Mem) (addr n w : Nat) :
    m.readBits false addr (n + 1) w = (m.readBits false addr n w).bind fun acc =>
      (m.bytes (addr + n)).map fun b => acc ||| ((b.setWidth w : BitVec w) <<< (8 * n)) := by
  unfold Mem.readBits
  rw [List.range_succ, List.foldlM_append]
  simp only [List.foldlM_cons, List.foldlM_nil, Mem.byteIndex, Bool.false_eq_true, ite_false]
  show Option.bind _ _ = Option.bind _ _
  congr 1
  funext acc
  cases m.bytes (addr + n) <;> rfl

/-- The bits `readBits` assembles: byte `j / 8`, bit `j % 8`, below `8 n` (and `w`). -/
theorem readBits_spec {m : Mem} {addr w : Nat} :
    ∀ n x, m.readBits false addr n w = some x →
      (∀ k < n, (m.bytes (addr + k)).isSome) ∧
      ∀ j, x.getLsbD j = (decide (j < w) && decide (j < 8 * n) &&
        ((m.bytes (addr + j / 8)).getD 0).getLsbD (j % 8)) := by
  intro n
  induction n with
  | zero =>
    intro x h
    simp only [Mem.readBits, List.range_zero, List.foldlM_nil] at h
    cases h
    exact ⟨fun k hk => absurd hk (Nat.not_lt_zero _), fun j => by simp⟩
  | succ n ih =>
    intro x h
    rw [readBits_succ] at h
    obtain ⟨acc, hacc, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h2
    obtain ⟨h1, h3⟩ := ih acc hacc
    refine ⟨fun k hk => ?_, fun j => ?_⟩
    · by_cases hkn : k < n
      · exact h1 k hkn
      · rw [show k = n by omega, hb]; rfl
    · rw [BitVec.getLsbD_or, h3, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
      by_cases hj : j < 8 * n
      · have hj2 : j < 8 * (n + 1) := by omega
        simp only [hj, hj2, decide_true, Bool.and_true, Bool.not_true, Bool.and_false,
          Bool.false_and, Bool.or_false]
      · by_cases hj3 : j < 8 * (n + 1)
        · have e1 : j / 8 = n := by omega
          have e2 : j - 8 * n = j % 8 := by omega
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

theorem readBits_some {m : Mem} {addr w : Nat} :
    ∀ n, (∀ k < n, (m.bytes (addr + k)).isSome) → ∃ x, m.readBits false addr n w = some x := by
  intro n
  induction n with
  | zero => intro _; exact ⟨0, rfl⟩
  | succ n ih =>
    intro h
    obtain ⟨acc, hacc⟩ := ih fun k hk => h k (by omega)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h n (by omega))
    rw [readBits_succ, hacc]
    exact ⟨acc ||| ((b.setWidth w : BitVec w) <<< (8 * n)), by simp [hb]⟩

/-- The two 8-byte halves of a 16-byte little-endian read. -/
theorem readBits_split {m : Mem} {A : Nat} {x : BitVec 128}
    (h : m.readBits false A 16 128 = some x) :
    m.readBits false A 8 64 = some (x.extractLsb' 0 64) ∧
      m.readBits false (A + 8) 8 64 = some (x.extractLsb' 64 64) := by
  obtain ⟨hs, hx⟩ := readBits_spec 16 x h
  obtain ⟨y, hy⟩ := readBits_some (w := 64) 8 fun k hk => hs k (by omega)
  obtain ⟨z, hz⟩ := readBits_some (w := 64) (addr := A + 8) 8 fun k hk => by
    rw [Nat.add_assoc]; exact hs (8 + k) (by omega)
  obtain ⟨-, hy'⟩ := readBits_spec 8 y hy
  obtain ⟨-, hz'⟩ := readBits_spec 8 z hz
  refine ⟨hy.trans (congrArg some ?_), hz.trans (congrArg some ?_)⟩
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [hy', BitVec.getLsbD_extractLsb', hx]
    simp [hj, show j < 128 by omega, show j < 8 * 16 by omega]
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [hz', BitVec.getLsbD_extractLsb', hx]
    have e1 : A + 8 + j / 8 = A + (64 + j) / 8 := by omega
    have e2 : j % 8 = (64 + j) % 8 := by omega
    simp [hj, show 64 + j < 128 by omega, show 64 + j < 8 * 16 by omega, e1, e2]

/-! ## Writing bytes -/

theorem byte_append (hi lo : BitVec 64) {k : Nat} (hk : k < 16) :
    (hi ++ lo).extractLsb' (8 * k) 8 =
      if k < 8 then lo.extractLsb' (8 * k) 8 else hi.extractLsb' (8 * (k - 8)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  by_cases h : k < 8
  · simp only [h, ite_true, BitVec.getLsbD_extractLsb', ht, decide_true, Bool.true_and,
      BitVec.getLsbD_append, show 8 * k + t < 64 by omega]
  · simp only [h, ite_false, BitVec.getLsbD_extractLsb', ht, decide_true, Bool.true_and,
      BitVec.getLsbD_append, show ¬ (8 * k + t < 64) by omega]
    exact congrArg _ (by omega)

/-- Two 8-byte writes of the halves are the 16-byte write. -/
theorem writeBits_split (m : Mem) (A : Nat) (lo hi : BitVec 64) :
    (m.writeBits false A 8 lo).writeBits false (A + 8) 8 hi = m.writeBits false A 16 (hi ++ lo) := by
  simp only [Mem.writeBits, Mem.byteIndex, Bool.false_eq_true, ite_false]
  congr 1
  funext a
  by_cases h1 : A + 8 ≤ a ∧ a < A + 8 + 8
  · rw [if_pos h1, if_pos (show A ≤ a ∧ a < A + 16 by omega),
      byte_append hi lo (show a - A < 16 by omega), if_neg (show ¬ (a - A < 8) by omega)]
    congr 3 <;> omega
  · rw [if_neg h1]
    by_cases h2 : A ≤ a ∧ a < A + 8
    · rw [if_pos h2, if_pos (show A ≤ a ∧ a < A + 16 by omega),
        byte_append hi lo (show a - A < 16 by omega), if_pos (show a - A < 8 by omega)]
    · rw [if_neg h2, if_neg (show ¬ (A ≤ a ∧ a < A + 16) by omega)]

/-! ## The split accesses -/

theorem checkAccess_split {m : Mem} {fl : MemFlags} {A : Nat}
    (h : m.checkAccess fl A 16 = .ok ()) :
    m.checkAccess fl A 8 = .ok () ∧ m.checkAccess fl (A + 8) 8 = .ok () := by
  unfold Mem.checkAccess at h ⊢
  by_cases hv : m.valid A 16 = true
  · rw [if_pos hv] at h
    have hal : fl.aligned = true → A % 16 = 0 := by
      intro ha
      by_cases hne : A % 16 = 0
      · exact hne
      · rw [if_pos (by simp [ha, hne])] at h; cases h
    rw [if_pos (valid_sub hv (Nat.le_refl _) (by omega)),
      if_pos (valid_sub hv (by omega) (by omega))]
    constructor <;> rw [if_neg] <;>
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and, Decidable.not_not] <;>
      intro ha <;> have := hal ha <;> omega
  · rw [if_neg hv] at h; split at h <;> cases h

theorem load_split {m : Mem} {fl : MemFlags} (hbig : (fl.endianness == some .big) = false)
    {A : Nat} {x : BitVec 128} (h : m.load fl A 16 (8 * 16) = .ok x) :
    m.load fl A 8 (8 * 8) = .ok (x.extractLsb' 0 64) ∧
      m.load fl (A + 8) 8 (8 * 8) = .ok (x.extractLsb' 64 64) := by
  simp only [Mem.load, hbig, Opt.Res.bind_eq_ok, Opt.Res.ofOption_eq_ok] at h ⊢
  obtain ⟨u, hc, hr⟩ := h
  obtain ⟨h1, h2⟩ := checkAccess_split hc
  obtain ⟨r1, r2⟩ := readBits_split hr
  exact ⟨⟨(), h1, r1⟩, ⟨(), h2, r2⟩⟩

theorem store_inv {w : Nat} {m : Mem} {fl : MemFlags} {a n : Nat} {x : BitVec w} {m' : Mem}
    (h : m.store fl a n x = .ok m') :
    m.checkAccess fl a n = .ok () ∧ m.readonlyAt a n = false ∧
      m' = m.writeBits (fl.endianness == some .big) a n x := by
  simp only [Mem.store, Opt.Res.bind_eq_ok] at h
  obtain ⟨u, hc, u2, hro, hw⟩ := h
  cases u
  simp only [Res.check] at hro
  split at hro
  · rename_i hr
    cases hw
    exact ⟨hc, by simpa using hr, rfl⟩
  · cases hro

theorem store_ok {w : Nat} {m : Mem} {fl : MemFlags} {a n : Nat} (x : BitVec w)
    (hc : m.checkAccess fl a n = .ok ()) (hr : m.readonlyAt a n = false) :
    m.store fl a n x = .ok (m.writeBits (fl.endianness == some .big) a n x) := by
  simp only [Mem.store, hc, Res.check, hr, Bool.not_false, ite_true]
  rfl

@[simp] theorem checkAccess_writeBits {w : Nat} (m : Mem) (big : Bool) (addr n : Nat)
    (x : BitVec w) (fl : MemFlags) (a k : Nat) :
    (m.writeBits big addr n x).checkAccess fl a k = m.checkAccess fl a k := rfl

@[simp] theorem readonlyAt_writeBits {w : Nat} (m : Mem) (big : Bool) (addr n : Nat)
    (x : BitVec w) (a k : Nat) :
    (m.writeBits big addr n x).readonlyAt a k = m.readonlyAt a k := rfl

theorem store_split {m : Mem} {fl : MemFlags} (hbig : (fl.endianness == some .big) = false)
    {A : Nat} {x : BitVec 128} {m' : Mem} (h : m.store fl A 16 x = .ok m') :
    ∃ m1, m.store fl A 8 (x.extractLsb' 0 64) = .ok m1 ∧
      m1.store fl (A + 8) 8 (x.extractLsb' 64 64) = .ok m' := by
  obtain ⟨hc, hro, rfl⟩ := store_inv h
  obtain ⟨h1, h2⟩ := checkAccess_split hc
  have hro1 : m.readonlyAt A 8 = false := by
    cases e : m.readonlyAt A 8
    · rfl
    · have := readonlyAt_sub (a := A) (n := 16) e (Nat.le_refl _) (by omega); simp_all
  have hro2 : m.readonlyAt (A + 8) 8 = false := by
    cases e : m.readonlyAt (A + 8) 8
    · rfl
    · have := readonlyAt_sub (a := A) (n := 16) e (by omega) (by omega); simp_all
  refine ⟨_, store_ok _ h1 hro1, ?_⟩
  rw [store_ok _ (by rw [checkAccess_writeBits]; exact h2) (by rw [readonlyAt_writeBits]; exact hro2),
    hbig, writeBits_split]
  have e : x.extractLsb' 64 64 ++ x.extractLsb' 0 64 = x := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
    by_cases hj2 : j < 64
    · simp [hj2]
    · simp [hj2, show j - 64 < 64 by omega]; exact congrArg _ (by omega)
  rw [e]

/-- The effective address of the high half, when the 16 bytes lie below `2^64`. -/
theorem effAddr_add8 (p : Val) (off : Int) (h : effAddr p off + 16 ≤ 2 ^ 64) :
    effAddr p (off + 8) = effAddr p off + 8 := by
  simp only [effAddr] at h ⊢
  omega

end Opt.Legal
