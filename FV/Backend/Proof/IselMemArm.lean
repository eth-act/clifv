import FV.Backend.Proof.RegallocOperands
import FV.Clif.Run

/-!
# CLIF memory ↔ Arm memory (memory family, M4Mem)

Byte-level facts relating `Clif.Mem.readBits`/`writeBits` (little-endian) to the Arm model's
`read_mem_bytes`/`write_mem_bytes` at the same (64-bit) addresses: a CLIF load of `n` bytes
whose bytes are the Arm bytes reads the Arm value (`readBits_getLsbD_eq`), and a store changes the
same bytes on both sides (`read_mem_write_mem_bytes`, `writeBits_bytes`).
-/

namespace Backend.Proof

/-- The step of `Clif.Mem.readBits` (little-endian). -/
def rbStep (g : Nat → Option (BitVec 8)) (w : Nat) (acc : BitVec w) (i : Nat) :
    Option (BitVec w) :=
  (g i).bind fun b => some (acc ||| (b.zeroExtend w <<< (8 * i)))

theorem foldlM_rbStep {g : Nat → Option (BitVec 8)} {w : Nat} :
    ∀ (n : Nat) (r : BitVec w), (List.range n).foldlM (rbStep g w) 0 = some r →
      (∀ i < n, (g i).isSome) ∧
      ∀ j, r.getLsbD j = (decide (j < w) && decide (j / 8 < n) && ((g (j / 8)).getD 0).getLsbD (j % 8))
  | 0, r, h => by
    simp only [List.range_zero, List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun j => ?_⟩
    simp
  | n + 1, r, h => by
    rw [List.range_succ, List.foldlM_append] at h
    cases hacc : (List.range n).foldlM (rbStep g w) 0 with
    | none => rw [hacc] at h; cases h
    | some acc =>
      rw [hacc] at h
      obtain ⟨ih1, ih2⟩ := foldlM_rbStep n acc hacc
      simp only [List.foldlM_cons, List.foldlM_nil, rbStep] at h
      cases hg : g n with
      | none => rw [hg] at h; cases h
      | some b =>
        rw [hg] at h
        simp only [Option.bind_some, Option.pure_def, Option.bind_eq_bind, Option.some.injEq] at h
        subst h
        refine ⟨fun i hi => ?_, fun j => ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
          · exact ih1 i hi
          · simp [hg]
        · rw [BitVec.getLsbD_or, ih2, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
          by_cases hjw : j < w
          · simp only [hjw, decide_true, Bool.true_and]
            by_cases hjn : j / 8 < n
            · have : j < 8 * n := by omega
              simp [hjn, this, show j / 8 < n + 1 by omega]
            · have hge : ¬ j < 8 * n := by omega
              by_cases hj8 : j / 8 = n
              · have hlt : j - 8 * n < 8 := by omega
                simp [hge, hj8, hg, show j - 8 * n = j % 8 by omega, show j % 8 < w by omega]
              · have : ¬ j - 8 * n < 8 := by omega
                simp [hjn, hge, show ¬ j / 8 < n + 1 by omega,
                  BitVec.getLsbD_of_ge b (j - 8 * n) (by omega)]
          · simp [hjw]

/-- A successful little-endian CLIF read of `n` bytes: every byte is initialised, and bit `j`
of the value is bit `j % 8` of byte `j / 8`. -/
theorem readBits_spec {m : Clif.Mem} {A n w : Nat} {r : BitVec w}
    (h : m.readBits false A n w = some r) :
    (∀ i < n, (m.bytes (A + i)).isSome) ∧
    ∀ j, r.getLsbD j = (decide (j < w) && decide (j / 8 < n) &&
      ((m.bytes (A + j / 8)).getD 0).getLsbD (j % 8)) := by
  have e : m.readBits false A n w = (List.range n).foldlM (rbStep (fun i => m.bytes (A + i)) w) 0 := by
    simp only [Clif.Mem.readBits, Clif.Mem.byteIndex, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [e] at h
  exact foldlM_rbStep n r h

/-- **Loads**: a CLIF read of `n` bytes at `A` whose bytes are the Arm bytes has the bits of
`read_mem_bytes n A`. -/
theorem readBits_getLsbD_eq {m : Clif.Mem} {s : Arm.ArmState} {A n : Nat} {r : BitVec (8 * n)}
    (h : m.readBits false A n (8 * n) = some r) (hA : A + n ≤ 2 ^ 64)
    (hb : ∀ i < n, ∀ b, m.bytes (A + i) = some b → Arm.read_mem (BitVec.ofNat 64 (A + i)) s = b)
    (j : Nat) : r.getLsbD j = (Arm.read_mem_bytes n (BitVec.ofNat 64 A) s).getLsbD j := by
  obtain ⟨h1, h2⟩ := readBits_spec h
  rw [h2, Arm.Memory.State.read_mem_bytes_eq_mem_read_bytes,
    Arm.Memory.getLsbD_read_bytes (by omega)]
  by_cases hj : j < 8 * n
  · have hi : j / 8 < n := by omega
    obtain ⟨b, hbj⟩ := Option.isSome_iff_exists.mp (h1 _ hi)
    have := hb _ hi b hbj
    simp only [hj, decide_true, hi, Bool.true_and, show j < n * 8 by omega, hbj, Option.getD_some]
    rw [← this, BitVec.ofNat_add]
    rfl
  · simp [hj, show ¬ j < n * 8 by omega]

/-- **Stores (Arm side)**: the byte at `a` after writing `n` bytes of `y` at `A` (no wrap). -/
theorem read_mem_write_mem_bytes {n A a : Nat} (y : BitVec (n * 8)) (s : Arm.ArmState)
    (hA : A + n ≤ 2 ^ 64) (ha : a < 2 ^ 64) :
    Arm.read_mem (BitVec.ofNat 64 a) (Arm.write_mem_bytes n (BitVec.ofNat 64 A) y s) =
      if A ≤ a ∧ a < A + n then y.extractLsb' (8 * (a - A)) 8
      else Arm.read_mem (BitVec.ofNat 64 a) s := by
  have hA' : A < 2 ^ 64 ∨ n = 0 := by omega
  rw [Arm.Memory.write_mem_bytes_eq_mem_write_bytes]
  show (Arm.Memory.write_bytes n (BitVec.ofNat 64 A) y s.mem) (BitVec.ofNat 64 a) = _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.add_zero, Arm.Memory.write_bytes_zero]
    rw [if_neg (by omega)]; rfl
  have hA64 : A < 2 ^ 64 := by omega
  have htA : (BitVec.ofNat 64 A).toNat = A := by simp [Nat.mod_eq_of_lt hA64]
  have hta : (BitVec.ofNat 64 a).toNat = a := by simp [Nat.mod_eq_of_lt ha]
  rw [Arm.Memory.write_bytes_eq (by rw [htA]; exact hA)]
  by_cases hin : A ≤ a ∧ a < A + n
  · rw [if_pos hin, if_neg (by rw [BitVec.lt_def, htA, hta]; omega),
      if_neg (by rw [htA, hta]; omega)]
    have hsub : (BitVec.ofNat 64 a - BitVec.ofNat 64 A).toNat = a - A := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, htA, hta]; exact hin.1), htA, hta]
    rw [hsub]
    rw [Arm.BitVec.extractLsByte_def, Nat.mul_comm (a - A) 8]
  · rw [if_neg hin]
    have : BitVec.ofNat 64 a < BitVec.ofNat 64 A ∨ (BitVec.ofNat 64 a).toNat ≥ (BitVec.ofNat 64 A).toNat + n := by
      rw [BitVec.lt_def, htA, hta]; omega
    rcases this with h | h
    · rw [if_pos h]; rfl
    · rw [if_neg (by rw [BitVec.lt_def, htA, hta] at *; omega), if_pos h]; rfl

/-- **Stores (CLIF side)**: the byte at `a` after `writeBits false A n x`. -/
theorem writeBits_bytes {m : Clif.Mem} {w : Nat} (A n : Nat) (x : BitVec w) (a : Nat) :
    (m.writeBits false A n x).bytes a =
      if A ≤ a ∧ a < A + n then some (x.extractLsb' (8 * (a - A)) 8) else m.bytes a := by
  simp [Clif.Mem.writeBits, Clif.Mem.byteIndex]

theorem writeBits_allocs {m : Clif.Mem} {w : Nat} (A n : Nat) (x : BitVec w) :
    (m.writeBits false A n x).allocs = m.allocs := rfl

theorem writeBits_symbols {m : Clif.Mem} {w : Nat} (A n : Nat) (x : BitVec w) :
    (m.writeBits false A n x).symbols = m.symbols := rfl

theorem writeBits_valid {m : Clif.Mem} {w : Nat} (A n : Nat) (x : BitVec w) (a k : Nat) :
    (m.writeBits false A n x).valid a k = m.valid a k := rfl

/-- Only the low `8 n` bits of a stored value matter. -/
theorem writeBits_setWidth {m : Clif.Mem} {w : Nat} (A n : Nat) (x : BitVec w) (hn : n * 8 ≤ w) :
    m.writeBits false A n x = m.writeBits false A n (x.setWidth (n * 8)) := by
  simp only [Clif.Mem.writeBits]
  congr 1
  funext a
  split
  · rename_i h
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, Clif.Mem.byteIndex,
      Bool.false_eq_true, ↓reduceIte, hk, decide_true, Bool.true_and]
    have : 8 * (a - A) + k < n * 8 := by omega
    simp [this]
  · rfl

end Backend.Proof
