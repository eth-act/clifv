import FV.Concurrency.ThreadRefine
import FV.Concurrency.ProgramWitness

/-!
# Non-vacuity of `ThreadRefine.realizes_of_threads`

The two returning threads of `ProgWitness` (`ret_correct`): each Arm thread's (empty) trace
refines the CLIF thread's return step, so `realizes_of_threads` derives `Realizes`, and
`program_correct` gives the multi-threaded `Clif.run` run with `Realizes` derived, not assumed.
-/

namespace Concurrency.ProgWitness

open Rel Prog ClifThread ProgE2E ThreadRefine

theorem evAt_ret (p : Nat × Nat) : evAt ([[]] : List (List (Ev SKind BVal))) p = none := by
  obtain ⟨j, k⟩ := p
  rcases j with _ | j <;> simp [evAt]

/-- The return step of a CLIF thread refines the empty Arm trace. -/
theorem ret_refines (i : Nat) :
    Refines Maps (fun _ => False) (fun _ _ => False) ([[]] : List (List (Ev SKind BVal)))
      (PA.tr i) id where
  ev p x h := by rw [evAt_ret] at h; cases h
  mono p _ hp := by rw [evAt_ret] at hp; cases hp
  shared p x h := by rw [evAt_ret] at h; cases h
  priv p y h := by simp [PA, evAt] at h
  len j h := by simp
  pair j h h2 := by simp at h2
  pair_inv p _ hp := by rw [evAt_ret] at hp; cases hp

/-- **Non-vacuity of `realizes_of_threads`**: `Realizes` for the two returning threads. -/
theorem ret_threads : ∃ (PC' : Traces TState SKind BVal) (φ : PEv → PEv), PC'.n = PA.n ∧
    (∀ i, PC'.st i 0 = s0 i) ∧ PC'.Runs (CStep env0 p0) ∧
    Realizes PA [] (fun _ => none) none2 none2 none2 PC' [] (fun _ => none) φ Obs :=
  realizes_of_threads (Priv := fun _ => False) (pairT := fun _ _ _ => False) wfA
    (fun _ _ _ _ => Iff.rfl) (List.prefix_refl _) (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun i hi => ⟨[[]], PC.st i, id, rfl, fun j hj => runsC i hi j hj, ret_refines i, rfl⟩)

/-- **`program_correct` with `Realizes` derived from per-thread refinements**: the two returning
threads; the multi-threaded `Clif.run` reaches both threads returned. -/
theorem ret_correct_threads : ∃ ts B, MTRun env0 p0 (s0, fun _ => none) (ts, B) := by
  obtain ⟨PC', φ, hn, hs0, hruns, hR⟩ := ret_threads
  obtain ⟨-, ts, B, h1, -⟩ := program_correct hR wfA (ret_raceFree _)
    (fun i hi j hj => absurd hj (Nat.not_lt_zero _)) consA (fun _ _ h => h.elim)
    (fun a _ ha => absurd (PA_dir a) ha) (fun _ _ h => h.elim) hruns hn hs0
  exact ⟨ts, B, h1⟩

/-! ## A thread with a private spill: `Refines` and `Refines.trans` -/

/-- An atomic load of `x` (address 8) reading 1. -/
def rS : Ev SKind BVal := ⟨.scR, .R, 8, 1, [some 1]⟩
/-- Its `ldar`. -/
def rT : Ev AKind BVal := ⟨.acqR, .R, 8, 1, [some 1]⟩
/-- A spill to the thread's frame (address 100). -/
def spill : Ev AKind BVal := ⟨.plainW, .W, 100, 8, []⟩

theorem evAt_one {α : Type} {a x : α} {p : Nat × Nat} (h : evAt [[a]] p = some x) :
    p = (0, 0) ∧ x = a := by
  obtain ⟨j, k⟩ := p
  rcases j with _ | j <;> rcases k with _ | k <;> simp [evAt] at h ⊢
  exact h.symm

theorem evAt_two {α : Type} {a b x : α} {p : Nat × Nat} (h : evAt [[a], [b]] p = some x) :
    (p = (0, 0) ∧ x = a) ∨ (p = (1, 0) ∧ x = b) := by
  obtain ⟨j, k⟩ := p
  rcases j with _ | _ | j <;> rcases k with _ | k <;> simp [evAt] at h ⊢
  · exact h.symm
  · exact h.symm

/-- **Non-vacuity of `Refines`**: the CLIF atomic load is realized by `str` (spill, private) then
`ldar`. -/
theorem refines_spill : Refines Maps (fun l => l = 100) (fun _ _ => False) [[rS]] [[spill], [rT]]
    (fun p => (p.1 + 1, p.2)) where
  ev p x h := by
    obtain ⟨rfl, rfl⟩ := evAt_one h
    exact ⟨rT, by simp [evAt], .inl rfl, rfl, rfl, rfl, rfl⟩
  mono p q hp hq hl := by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hp
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hq
    obtain ⟨rfl, -⟩ := evAt_one hx
    obtain ⟨rfl, -⟩ := evAt_one hy
    exact absurd hl (Lt.irrefl _)
  shared p x h := by
    obtain ⟨-, rfl⟩ := evAt_one h
    simp [rS]
  priv p y h hW _ := by
    rcases evAt_two h with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · rfl
    · cases hW
  len j h := by simp at h; subst h; simp
  pair j h h2 := by simp at h; subst h; simp at h2
  pair_inv p q hp _ hpr := hpr.elim

/-- **Non-vacuity of `Refines.trans`**: the identity layer composed with `refines_spill`. -/
theorem refines_trans_spill :
    Refines (fun a c => ∃ b, a = b ∧ Maps b c) (fun l => False ∨ l = 100) (fun _ _ => False)
      [[rS]] [[spill], [rT]] (fun p => (p.1 + 1, p.2)) := by
  have hid : Refines (fun a b : SKind => a = b) (fun _ => False) (StepPair [[rS]]) [[rS]] [[rS]]
      id :=
    { ev := fun p x h => ⟨x, h, rfl, rfl, rfl, rfl, rfl⟩
      mono := fun _ _ _ _ hl => hl
      shared := fun _ _ _ _ h => h
      priv := fun p y h _ hn => absurd rfl (hn p (by rw [h]; rfl))
      len := fun j h => by simp at h; subst h; simp
      pair := fun j h h2 => by simp at h; subst h; simp at h2
      pair_inv := fun p q _ _ hpr => by
        obtain ⟨j, rfl, rfl, hj, h2⟩ := hpr
        exact ⟨j, rfl, rfl⟩ }
  exact hid.trans refines_spill

end Concurrency.ProgWitness
