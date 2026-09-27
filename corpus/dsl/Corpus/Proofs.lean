import Corpus.Arith
import Corpus.Vectors
import Corpus.Errors
import Corpus.Maps

/-! User-level correctness proofs about shallow definitions (never about the deep AST). -/

namespace Corpus
open DSL

/-- `absDiff` computes `|a - b|` and never fails. -/
theorem absDiff_spec (a b : BitVec 32) :
    absDiff a b = .ok (if b ≤ a then a - b else b - a) := by
  unfold absDiff
  by_cases h : b ≤ a
  · have : b.ule a = true := by simpa [BitVec.ule, BitVec.le_def] using h
    simp [this, h]
  · have : b.ule a = false := by simpa [BitVec.ule, BitVec.le_def] using h
    simp [this, h]

/-- `safeDiv` fails exactly on a zero divisor, with user error 7. -/
theorem safeDiv_error_iff (a b : BitVec 64) (e : Err) :
    safeDiv a b = .error e ↔ b = 0 ∧ e = .user 7 := by
  unfold safeDiv
  by_cases h : b = 0
  · subst h; simp [eq_comm]
  · have hb : (b == 0) = false := by simpa using h
    simp only [hb, Bool.false_eq_true, ite_false]
    constructor
    · intro he
      unfold Ops.udiv at he
      split at he
      · exact absurd ‹_› h
      · cases he
    · intro ⟨hb0, _⟩; exact absurd hb0 h

/-- `sumChecked` cannot overflow when every element is below `2^62`,
proven with the loop-invariant rule `Ops.forRange_ok`. -/
theorem sumChecked_ok_of_small (xs : Vector (BitVec 64) 4)
    (hs : ∀ i (h : i < 4), xs[i].toNat < 2 ^ 62) :
    ∃ r, sumChecked xs = .ok r ∧ r.toNat ≤ 4 * 2 ^ 62 := by
  unfold sumChecked
  obtain ⟨r, hr, hP⟩ := Ops.forRange_ok (n := 4) (init := (0 : BitVec 64))
    (P := fun i (acc : BitVec 64) => acc.toNat ≤ i * 2 ^ 62)
    (f := fun i acc => Ops.vget xs i >>= fun t => Ops.addC acc t >>= fun acc => pure acc)
    (by simp)
    (by
      intro i hi acc hacc
      have hi' : (BitVec.ofNat 64 i).toNat = i := by
        simp; omega
      have hx := hs i hi
      have hlt : acc.toNat + xs[i].toNat < 2 ^ 64 := by omega
      refine ⟨acc + xs[i], ?_, ?_⟩
      · rw [Ops.vget_ok xs _ (by omega)]
        simp only [Ops.ok_bind, hi']
        rw [Ops.addC_ok hlt]; rfl
      · rw [BitVec.toNat_add, Nat.mod_eq_of_lt hlt]
        rw [Nat.succ_mul]; omega)
  exact ⟨r, by simp only [Ops.pure_eq_ok] at hr ⊢; rw [hr]; rfl, by simpa using hP⟩

/-- The last write to key 1 wins, using the map laws. -/
theorem lookup_one (a b : BitVec 64) : lookup 1 a b = .ok (a + b) := by
  unfold lookup
  simp [Ops.mapGet]

/-- A key absent from every insert is `notFound`. -/
theorem lookup_other (k : BitVec 32) (hk1 : k ≠ 1) (hk2 : k ≠ 2) (a b : BitVec 64) :
    lookup k a b = .error .notFound := by
  unfold lookup
  have h1 : ¬ k = 1#32 := hk1
  have h2 : ¬ k = 2#32 := hk2
  simp [Ops.mapGet, h1, h2]

end Corpus
