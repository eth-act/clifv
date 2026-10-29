module

public import FV.Concurrency.PrivCohT
public import FV.Concurrency.ThreadRefineWitness

@[expose] public section

/-!
# Witnesses: time-varying private sets (#473, (iv))

* `refinesT_reuse`: a thread spills to address 100 (private while the spill is live) and later
  uses 100 as a CLIF stack slot (a CLIF store, then a CLIF load: shared) — a `RefinesT` with
  `PrivAt` private at the spill's position only; `not_refines_reuse`: no `Refines` with a fixed
  private set realizes it;
* `ret_threadsT`: `realizes_of_threads_privT` on the two returning threads of `ProgWitness`
  (through `Refines.toT`), its premises (SC per location, initial writes first, `StackDisjoint`)
  discharged.
-/

namespace Concurrency.PrivCohT.Witness

open Rel Prog ClifThread ProgE2E ThreadRefine ProgWitness

/-- A spill at 100. -/
def spillW : Ev AKind BVal := ⟨.plainW, .W, 100, 8, [some 0]⟩
/-- The CLIF store to the slot at 100 and its `str`. -/
def stS : Ev SKind BVal := ⟨.naW, .W, 100, 8, [some 1]⟩
def stT : Ev AKind BVal := ⟨.plainW, .W, 100, 8, [some 1]⟩
/-- The CLIF load of the slot and its `ldr`. -/
def ldS : Ev SKind BVal := ⟨.naR, .R, 100, 8, [some 1]⟩
def ldT : Ev AKind BVal := ⟨.plainR, .R, 100, 8, [some 1]⟩

def trSW : List (List (Ev SKind BVal)) := [[stS], [ldS]]
def trTW : List (List (Ev AKind BVal)) := [[spillW], [stT], [ldT]]
def ψW : Nat × Nat → Nat × Nat := fun p => (p.1 + 1, p.2)
/-- 100 is private at the spill's position, shared after. -/
def PrivAtW : Nat × Nat → Nat → Prop := fun q l => q.1 = 0 ∧ l = 100

theorem evAt_S {p : Nat × Nat} {x : Ev SKind BVal} (h : evAt trSW p = some x) :
    (p = (0, 0) ∧ x = stS) ∨ (p = (1, 0) ∧ x = ldS) := by
  obtain ⟨j, k⟩ := p
  rcases j with _ | _ | j <;> rcases k with _ | k <;> simp [evAt, trSW] at h ⊢
  · exact h.symm
  · exact h.symm

theorem evAt_T {p : Nat × Nat} {y : Ev AKind BVal} (h : evAt trTW p = some y) :
    (p = (0, 0) ∧ y = spillW) ∨ (p = (1, 0) ∧ y = stT) ∨ (p = (2, 0) ∧ y = ldT) := by
  obtain ⟨j, k⟩ := p
  rcases j with _ | _ | _ | j <;> rcases k with _ | k <;> simp [evAt, trTW] at h ⊢
  · exact h.symm
  · exact h.symm
  · exact h.symm

/-- **A slot reused after a spill** (module doc). -/
theorem refinesT_reuse : RefinesT Maps (fun _ => False) PrivAtW (fun _ _ => False) trSW trTW ψW where
  ev p x h := by
    rcases evAt_S h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨stT, by simp [evAt, trTW, ψW], rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨ldT, by simp [evAt, trTW, ψW], rfl, rfl, rfl, rfl, rfl⟩
  mono p q _ _ hl := by
    simp only [ψW]
    rcases hl with hl | ⟨h1, h2⟩
    · exact .inl (by omega)
    · exact .inr ⟨by omega, h2⟩
  len j h := by
    rcases j with _ | _ | j
    · simp [trSW]
    · simp [trSW]
    · simp [trSW] at h; omega
  pair j h h2 := by
    rcases j with _ | _ | j
    · simp [trSW] at h2
    · simp [trSW] at h2
    · simp [trSW] at h; omega
  pair_inv _ _ _ _ h := h.elim
  shared p x h _ := by
    rintro ⟨h0, -⟩
    simp [ψW] at h0
  priv p y h hW hu := by
    rcases evAt_T h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact absurd rfl (hu (0, 0) (by simp [evAt, trSW]))
    · exact absurd rfl (hu (1, 0) (by simp [evAt, trSW]))
  fresh0 _ _ _ _ h := h.elim
  fresh p x h hR q y hy hW hl hlt hu := by
    rcases evAt_S h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hR
    · refine ⟨(0, 0), stS, by simp [evAt, trSW], rfl, rfl, ?_, .inl (by simp [ψW])⟩
      rcases evAt_T hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inl (by simp [ψW])
      · exact absurd rfl (hu (0, 0) (by simp [evAt, trSW]))
      · exact absurd rfl (hu (1, 0) (by simp [evAt, trSW]))

/-- **No fixed private set realizes the reuse**: the spill must be private, the CLIF store at the
same address shared. -/
theorem not_refines_reuse (Priv : Nat → Prop) (pairT : Nat × Nat → Nat × Nat → Prop)
    (ψ : Nat × Nat → Nat × Nat) : ¬ Refines Maps Priv pairT trSW trTW ψ := by
  intro h
  have hP : Priv 100 := h.priv (0, 0) spillW (by simp [evAt, trTW]) rfl fun p hp e => by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hp
    obtain ⟨y, hy, -, -, -, -, hv⟩ := h.ev p x hx
    rw [e] at hy
    simp [evAt, trTW] at hy
    subst hy
    rcases evAt_S hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [spillW, stS, ldS] at hv
  exact h.shared (0, 0) stS (by simp [evAt, trSW]) (by simp [stS]) hP

/-- The execution of `ProgWitness`'s returning threads is SC per location (it has no events). -/
theorem hintA : Acyclic (union (PA.exec [] none2 none2 none2).poLoc
    (PA.exec [] none2 none2 none2).com) := by
  have h : ∀ a b, ¬ union (PA.exec [] none2 none2 none2).poLoc (PA.exec [] none2 none2 none2).com a b := by
    rintro a b (⟨-, -, hF, -⟩ | h | h | ⟨w, h, -⟩)
    · exact hF (PA_dir a)
    · exact h
    · exact h
    · exact h
  intro a hc
  cases hc with
  | single hb => exact h _ _ hb
  | tail _ hb => exact h _ _ hb

/-- **Non-vacuity of `realizes_of_threads_privT`**: `Realizes` for the two returning threads. -/
theorem ret_threadsT : ∃ (PC' : Traces TState SKind BVal) (φ : PEv → PEv), PC'.n = PA.n ∧
    (∀ i, PC'.st i 0 = s0 i) ∧ PC'.Runs (CStep env0 p0) ∧
    Realizes PA [] (fun _ => none) none2 none2 none2 PC' [] (fun _ => none) φ Obs :=
  realizes_of_threads_privT (Priv0 := fun _ _ => False) (PrivAt := fun _ _ _ => False)
    (pairT := fun _ _ _ => False) wfA hintA (fun _ _ h => h) (fun _ _ _ _ => Iff.rfl)
    (List.prefix_refl _) (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun _ _ _ _ _ _ _ _ _ h => h.elim (fun h => h) fun ⟨_, h⟩ => h)
    (fun i hi => ⟨[[]], PC.st i, id, rfl, fun j hj => runsC i hi j hj,
      Refines.toT (ret_refines i), rfl⟩)

end Concurrency.PrivCohT.Witness
