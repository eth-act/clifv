import FV.Backend.Proof.DeadCleanupStructure

namespace Backend.DeadCleanup

/-- The scan keeps a non-pure first instruction first. -/
theorem scan_head (n : Nat) (i : MInst) (ms : List MInst) (live : List Nat)
    (hp : pureForm i = false) :
    (scan n (i :: ms) live).1 = i :: (scan n ms live).1 := by
  simp [scan, discard, hp]

/-- An exceptional instruction confined to position zero cannot move away
from position zero when all other instructions satisfy a positional-free fact. -/
theorem scan_positions (n : Nat) (ms : List MInst) (live : List Nat)
    (P Q : MInst → Prop)
    (h : ∀ k i, ms[k]? = some i → P i ∨ (k = 0 ∧ Q i))
    (hQ : ∀ i, Q i → pureForm i = false) :
    ∀ k i, (scan n ms live).1[k]? = some i → P i ∨ (k = 0 ∧ Q i) := by
  cases ms with
  | nil => simp [scan]
  | cons a tail =>
    have htail : ∀ i ∈ tail, P i := by
      intro i hi
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
      rcases h (k + 1) i (by simpa using hk) with hp | ⟨hz, _⟩
      · exact hp
      · omega
    have hkept : ∀ i ∈ (scan n tail live).1, P i :=
      fun i hi => htail i ((scan_sublist n tail live).subset hi)
    rcases h 0 a rfl with ha | ⟨_, hqa⟩
    · simp only [scan]
      split
      · intro k i hi
        exact .inl (hkept i (List.mem_of_getElem? hi))
      · intro k i hi
        cases k with
        | zero => cases hi; exact .inl ha
        | succ k => exact .inl (hkept i (List.mem_of_getElem? hi))
    · rw [scan_head n a tail live (hQ a hqa)]
      intro k i hi
      cases k with
      | zero => cases hi; exact .inr ⟨rfl, hqa⟩
      | succ k => exact .inl (hkept i (List.mem_of_getElem? hi))

/-- Taking the prefix before the final element is monotone for sublists. -/
theorem dropLast_sublist_of {α : Type} {xs ys : List α} (h : xs.Sublist ys) :
    xs.dropLast.Sublist ys.dropLast := by
  induction h with
  | slnil => simp
  | @cons xs ys a h ih =>
    cases ys with
    | nil => cases h; simp
    | cons b tail => simpa using ih.cons a
  | @cons_cons xs ys a h ih =>
    cases xs with
    | nil => simp
    | cons b tail =>
      cases ys with
      | nil => cases h
      | cons c rest => simpa using ih.cons_cons a

/-- A real ABI entry stays at position zero while its dead successor is removed. -/
example : (scan 4 [.args [], deadMvn, liveBic, liveReturn] [3]).1 =
    [.args [], liveBic, liveReturn] := by decide

end Backend.DeadCleanup
