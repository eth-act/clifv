import FV.Clif.Run

/-!
# Byte-level memory lemmas

Little-endian `writeBits`/`readBits` round trips, framing (bytes outside a write are
unchanged), and well-formedness of the bump allocator (`MemWF`: live allocations are sorted,
pairwise disjoint, below `next`, and `next ≤ 2^64`).
-/

set_option autoImplicit false

namespace Compile.Proof

open Clif

/-! ## Reading and writing bytes -/

theorem foldlM_congr {α β : Type} {f g : β → α → Option β} :
    ∀ (l : List α) (b : β), (∀ a ∈ l, ∀ b, f b a = g b a) → l.foldlM f b = l.foldlM g b
  | [], _, _ => rfl
  | a :: l, b, h => by
    simp only [List.foldlM_cons]
    rw [h a List.mem_cons_self b]
    cases g b a with
    | none => rfl
    | some b' => exact foldlM_congr l b' fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem readBits_congr {m m' : Mem} {addr n w : Nat}
    (h : ∀ i, i < n → m'.bytes (addr + i) = m.bytes (addr + i)) :
    m'.readBits false addr n w = m.readBits false addr n w := by
  unfold Mem.readBits
  apply foldlM_congr
  intro i hi acc
  simp only [Mem.byteIndex, Bool.false_eq_true, ↓reduceIte]
  rw [h i (List.mem_range.1 hi)]

theorem pow8 (k : Nat) : 2 ^ (8 * k) = 256 ^ k := by rw [Nat.pow_mul]

theorem step_nat (x k n : Nat) (hk : k + 1 ≤ n) :
    (x % 2 ^ (8 * k) % 2 ^ (8 * n)) ||| ((x / 2 ^ (8 * k) % 2 ^ 8 % 2 ^ (8 * n)) <<< (8 * k) % 2 ^ (8 * n))
      = x % 2 ^ (8 * (k + 1)) % 2 ^ (8 * n) := by
  generalize hA : x % 2 ^ (8 * k) = A
  generalize hB : x / 2 ^ (8 * k) % 2 ^ 8 = B
  generalize hP : 2 ^ (8 * k) = P
  have hAlt : A < P := hA ▸ hP ▸ Nat.mod_lt _ (Nat.two_pow_pos _)
  have hBlt : B < 256 := hB ▸ Nat.mod_lt _ (Nat.two_pow_pos _)
  have hk1 : 2 ^ (8 * (k + 1)) = P * 256 := by rw [← hP, Nat.mul_succ, Nat.pow_add]
  have hkn : P * 256 ≤ 2 ^ (8 * n) := hk1 ▸ Nat.pow_le_pow_right (by decide) (by omega)
  have hmod : x % 2 ^ (8 * (k + 1)) = A + P * B := by
    rw [← hA, ← hB, ← hP, pow8, pow8, Nat.mod_pow_succ, Nat.mul_comm]
  have hBP : B * P < P * 256 := by rw [Nat.mul_comm]; exact Nat.mul_lt_mul_of_pos_left hBlt (by omega)
  have hBP' : P * B < P * 256 := by rw [Nat.mul_comm]; exact hBP
  have hP1 : 1 ≤ P := by omega
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hAlt (by omega)),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hBlt (by omega)),
    Nat.shiftLeft_eq, hP, Nat.mul_comm B P, hmod,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hBP' hkn),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega : A + P * B < P * 256) hkn),
    Nat.or_comm, ← hP, ← Nat.two_pow_add_eq_or_of_lt (hP ▸ hAlt), Nat.add_comm]

/-- The byte decomposition of `x` reads back as `x`. -/
theorem readBits_of_bytes {m : Mem} {addr n : Nat} (x : Nat) (hx : x < 2 ^ (8 * n))
    (h : ∀ i, i < n → m.bytes (addr + i) = some (BitVec.ofNat 8 (x / 2 ^ (8 * i)))) :
    m.readBits false addr n (8 * n) = some (BitVec.ofNat (8 * n) x) := by
  unfold Mem.readBits
  suffices H : ∀ k, k ≤ n → (List.range k).foldlM (init := (0 : BitVec (8 * n)))
      (fun acc i => do
        let b ← m.bytes (addr + Mem.byteIndex false n i)
        pure (acc ||| (b.zeroExtend (8 * n) <<< (8 * i)))) =
      some (BitVec.ofNat (8 * n) (x % 2 ^ (8 * k))) by
    rw [H n (Nat.le_refl _), Nat.mod_eq_of_lt hx]
  intro k hk
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [List.range_succ, List.foldlM_append, ih (by omega)]
    simp only [List.foldlM_cons, List.foldlM_nil, Mem.byteIndex, Bool.false_eq_true,
      ↓reduceIte, h k (by omega), bind, Option.bind, pure]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft,
      BitVec.toNat_setWidth]
    exact step_nat x k n hk

theorem readBits_congr' {m m' : Mem} {big : Bool} {addr n w : Nat}
    (h : ∀ i, i < n → m'.bytes (addr + i) = m.bytes (addr + i)) :
    m'.readBits big addr n w = m.readBits big addr n w := by
  unfold Mem.readBits
  apply foldlM_congr
  intro i hi acc
  have hi := List.mem_range.1 hi
  have : Mem.byteIndex big n i < n := by unfold Mem.byteIndex; split <;> omega
  rw [h _ this]

theorem writeBits_in {m : Mem} {addr n w : Nat} (x : BitVec w) {i : Nat} (hi : i < n) :
    (m.writeBits false addr n x).bytes (addr + i) = some (x.extractLsb' (8 * i) 8) := by
  simp [Mem.writeBits, Mem.byteIndex, hi]

theorem writeBits_out {m : Mem} {big : Bool} {addr n w : Nat} (x : BitVec w) {a : Nat}
    (h : a < addr ∨ addr + n ≤ a) : (m.writeBits big addr n x).bytes a = m.bytes a := by
  simp only [Mem.writeBits]
  rw [ite_eq_right_iff.2 (fun h' => by omega)]

@[simp] theorem writeBits_allocs {m : Mem} {big : Bool} {addr n w : Nat} (x : BitVec w) :
    (m.writeBits big addr n x).allocs = m.allocs := rfl

@[simp] theorem writeBits_next {m : Mem} {big : Bool} {addr n w : Nat} (x : BitVec w) :
    (m.writeBits big addr n x).next = m.next := rfl

theorem extract_byte {w : Nat} (x : BitVec w) (i : Nat) :
    x.extractLsb' (8 * i) 8 = BitVec.ofNat 8 (x.toNat / 2 ^ (8 * i)) := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftRight_eq_div_pow]

/-- Store then load of the same bytes. -/
theorem readBits_writeBits (m : Mem) (addr n : Nat) (x : BitVec (8 * n)) :
    (m.writeBits false addr n x).readBits false addr n (8 * n) = some x := by
  rw [readBits_of_bytes x.toNat x.isLt (fun i hi => by rw [writeBits_in x hi, extract_byte])]
  simp

/-! ## Allocation well-formedness -/

/-- The live allocations of a bump-allocated memory. -/
structure MemWF (m : Mem) : Prop where
  fits : m.next ≤ 2 ^ 64
  below : ∀ a ∈ m.allocs, a.base + a.size < m.next
  sorted : m.allocs.Pairwise (fun x y => y.base + y.size < x.base)

theorem pairwise_mem {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a = b ∨ R a b ∨ R b a
  | [], _, _, _, ha, _ => by simp at ha
  | c :: l, h, a, b, ha, hb => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with ha' | ha'
    · rcases List.mem_cons.1 hb with hb' | hb'
      · exact .inl (ha'.trans hb'.symm)
      · subst ha'; exact .inr (.inl (h.1 _ hb'))
    · rcases List.mem_cons.1 hb with hb' | hb'
      · subst hb'; exact .inr (.inr (h.1 _ ha'))
      · exact pairwise_mem h.2 ha' hb'

theorem MemWF.disj {m : Mem} (hm : MemWF m) {a b : Alloc} (ha : a ∈ m.allocs)
    (hb : b ∈ m.allocs) (hne : a.base ≠ b.base) :
    a.base + a.size ≤ b.base ∨ b.base + b.size ≤ a.base := by
  rcases pairwise_mem hm.sorted ha hb with rfl | h | h
  · exact absurd rfl hne
  · right; omega
  · left; omega

theorem MemWF.eq_of_base {m : Mem} (hm : MemWF m) {a b : Alloc} (ha : a ∈ m.allocs)
    (hb : b ∈ m.allocs) (he : a.base = b.base) : a = b := by
  rcases pairwise_mem hm.sorted ha hb with h | h | h
  · exact h
  · omega
  · omega

theorem alignUp16 (n : Nat) : n ≤ Mem.alignUp n 16 ∧ Mem.alignUp n 16 % 16 = 0 ∧
    Mem.alignUp n 16 < n + 16 := by
  unfold Mem.alignUp; omega

theorem alloc_fst (m : Mem) (size align : Nat) (h : align ≤ 16) :
    (m.alloc size align).1 = Mem.alignUp m.next 16 := by
  simp [Mem.alloc, Nat.max_eq_right h]

theorem alloc_snd (m : Mem) (size align : Nat) (h : align ≤ 16) :
    (m.alloc size align).2 =
      { m with allocs := ⟨Mem.alignUp m.next 16, size⟩ :: m.allocs,
               next := Mem.alignUp m.next 16 + size + 16 } := by
  simp [Mem.alloc, Nat.max_eq_right h]

theorem fits_iff (m : Mem) : m.fits = true ↔ m.next ≤ 2 ^ 64 := by simp [Mem.fits]

/-- A successful allocation: well-formed, fresh, aligned, below `2^64`. -/
theorem MemWF.alloc {m : Mem} (hm : MemWF m) {size align : Nat} (h16 : align ≤ 16)
    (hf : (m.alloc size align).2.fits = true) :
    MemWF (m.alloc size align).2 ∧ m.next ≤ (m.alloc size align).1 ∧
      (m.alloc size align).1 % 16 = 0 ∧ (m.alloc size align).1 + size < 2 ^ 64 ∧
      (⟨(m.alloc size align).1, size⟩ : Alloc) ∈ (m.alloc size align).2.allocs ∧
      (m.alloc size align).2.allocs = ⟨(m.alloc size align).1, size⟩ :: m.allocs ∧
      (m.alloc size align).2.bytes = m.bytes := by
  have hf' : Mem.alignUp m.next 16 + size + 16 ≤ 2 ^ 64 := by
    rw [fits_iff, alloc_snd m size align h16] at hf; exact hf
  obtain ⟨h1, h2, h3⟩ := alignUp16 m.next
  rw [alloc_fst m size align h16, alloc_snd m size align h16]
  refine ⟨⟨by simp; omega, fun a ha => ?_, ?_⟩, h1, h2, by omega, by simp, rfl, rfl⟩
  · simp at ha
    rcases ha with rfl | ha
    · simp
    · have := hm.below a ha; simp; omega
  · rw [List.pairwise_cons]
    exact ⟨fun a ha => by have := hm.below a ha; simp; omega, hm.sorted⟩

theorem MemWF.writeBits {m : Mem} (hm : MemWF m) {big : Bool} {addr n w : Nat} (x : BitVec w) :
    MemWF (m.writeBits big addr n x) := ⟨hm.fits, hm.below, hm.sorted⟩

theorem MemWF.free {m : Mem} (hm : MemWF m) (bases : List Nat) : MemWF (m.free bases) :=
  ⟨hm.fits, fun a ha => hm.below a (List.mem_filter.1 ha).1, hm.sorted.filter _⟩

/-! ## Keeping an allocation intact -/

/-- `a` stays live with the same bytes. -/
def Keeps (m m' : Mem) (a : Alloc) : Prop :=
  a ∈ m.allocs → a ∈ m'.allocs ∧ ∀ x, a.base ≤ x → x < a.base + a.size → m'.bytes x = m.bytes x

theorem Keeps.refl (m : Mem) (a : Alloc) : Keeps m m a := fun h => ⟨h, fun _ _ _ => rfl⟩

theorem Keeps.trans {m₁ m₂ m₃ : Mem} {a : Alloc} (h₁ : Keeps m₁ m₂ a) (h₂ : Keeps m₂ m₃ a) :
    Keeps m₁ m₃ a := fun ha =>
  ⟨(h₂ (h₁ ha).1).1, fun x h h' => by rw [(h₂ (h₁ ha).1).2 x h h', (h₁ ha).2 x h h']⟩

theorem Keeps.alloc (m : Mem) (size align : Nat) (h16 : align ≤ 16) (a : Alloc) :
    Keeps m (m.alloc size align).2 a := fun ha => by
  rw [alloc_snd m size align h16]; exact ⟨List.mem_cons_of_mem _ ha, fun _ _ _ => rfl⟩

theorem Keeps.writeBits {m : Mem} (hm : MemWF m) {big : Bool} {addr n w : Nat} (x : BitVec w)
    {a b : Alloc} (hb : b ∈ m.allocs) (hin : b.base ≤ addr ∧ addr + n ≤ b.base + b.size)
    (hne : a.base ≠ b.base) : Keeps m (m.writeBits big addr n x) a := fun ha =>
  ⟨ha, fun y h1 h2 => by
    apply writeBits_out
    rcases hm.disj ha hb hne with h | h <;> omega⟩

theorem Keeps.free {m : Mem} (bases : List Nat) {a : Alloc} (h : a.base ∉ bases) :
    Keeps m (m.free bases) a := fun ha =>
  ⟨List.mem_filter.2 ⟨ha, by simpa using h⟩, fun _ _ _ => rfl⟩

theorem valid_of_mem {m : Mem} {a : Alloc} {addr n : Nat} (ha : a ∈ m.allocs)
    (hin : a.base ≤ addr ∧ addr + n ≤ a.base + a.size) : m.valid addr n = true := by
  simp only [Mem.valid, List.any_eq_true]
  exact ⟨a, ha, by simp [Alloc.contains]; omega⟩

theorem load_keeps {m m' : Mem} {flags : MemFlags} {addr n w : Nat} {a : Alloc}
    (ha : a ∈ m.allocs) (hin : a.base ≤ addr ∧ addr + n ≤ a.base + a.size) (hk : Keeps m m' a) :
    m'.load flags addr n w = m.load flags addr n w := by
  obtain ⟨ha', hb⟩ := hk ha
  simp only [Mem.load, Mem.checkAccess, valid_of_mem ha hin, valid_of_mem ha' hin, ↓reduceIte]
  rw [readBits_congr' (fun i hi => hb _ (by omega) (by omega))]

theorem store_eq {m : Mem} {flags : MemFlags} {addr n w : Nat} (x : BitVec w) {a : Alloc}
    (ha : a ∈ m.allocs) (hin : a.base ≤ addr ∧ addr + n ≤ a.base + a.size)
    (hal : flags.aligned = true → addr % n = 0) :
    m.store flags addr n x = .ok (m.writeBits (flags.endianness == some .big) addr n x) := by
  simp only [Mem.store, Mem.checkAccess, valid_of_mem ha hin, ↓reduceIte]
  cases h : flags.aligned
  · rfl
  · simp [hal h]

theorem load_eq {m : Mem} {flags : MemFlags} {addr n w : Nat} {a : Alloc} {v : BitVec w}
    (ha : a ∈ m.allocs) (hin : a.base ≤ addr ∧ addr + n ≤ a.base + a.size)
    (hal : flags.aligned = true → addr % n = 0)
    (hr : m.readBits (flags.endianness == some .big) addr n w = some v) :
    m.load flags addr n w = .ok v := by
  simp only [Mem.load, Mem.checkAccess, valid_of_mem ha hin, ↓reduceIte, hr]
  cases h : flags.aligned
  · rfl
  · simp [hal h]

end Compile.Proof
