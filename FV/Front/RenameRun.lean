module

public import FV.Front.RenameStep

@[expose] public section

/-!
# Renaming commutes with the CLIF semantics (T7d)

**`Clif.runLoop_ren`**: running the renamed program (`Program.rename σ.fwd`) in the renamed
environment (`Env.ren σ`) from the renamed state (`State.ren σ`) has the outcome of the original
run, its memory renamed (`Outcome.ren σ`), up to the messages of `stuck` (`Outcome.erase`).
Corollaries: a return or a trap of either run is the same return (memories related by
`Mem.ren`) or trap of the other.
-/

namespace Clif

theorem runLoop_ren (σ : Ren) (E : Env) (p : Program) (n : Nat) (s : State) :
    (runLoop (E.ren σ) (p.rename σ.fwd) n (s.ren σ)).erase = ((runLoop E p n s).ren σ).erase := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have h := step_ren σ E p s
    rw [runLoop_succ, runLoop_succ]
    cases hs : step E p s <;> cases hr : step (E.ren σ) (p.rename σ.fwd) (s.ren σ) <;>
      simp only [hs, hr, StepResult.ren_next, StepResult.ren_done, StepResult.ren_trapped,
        StepResult.ren_stuck, StepResult.erase_next, StepResult.erase_done,
        StepResult.erase_trapped, StepResult.erase_stuck, StepResult.next.injEq,
        StepResult.done.injEq, StepResult.trapped.injEq, reduceCtorEq] at h ⊢
    · subst h; exact ih _
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · subst h; rfl
    · rfl

/-- A return of the original run is a return of the renamed one. -/
theorem runLoop_ren_returned (σ : Ren) (E : Env) (p : Program) (n : Nat) (s : State)
    {vals : List Val} {m : Mem} (h : runLoop E p n s = .returned vals m) :
    runLoop (E.ren σ) (p.rename σ.fwd) n (s.ren σ) = .returned vals (m.ren σ) := by
  have hr := runLoop_ren σ E p n s
  rw [h] at hr
  revert hr
  cases runLoop (E.ren σ) (p.rename σ.fwd) n (s.ren σ) <;> simp

/-- A trap of the original run is a trap of the renamed one. -/
theorem runLoop_ren_trapped (σ : Ren) (E : Env) (p : Program) (n : Nat) (s : State)
    {c : TrapCode} (h : runLoop E p n s = .trapped c) :
    runLoop (E.ren σ) (p.rename σ.fwd) n (s.ren σ) = .trapped c := by
  have hr := runLoop_ren σ E p n s
  rw [h] at hr
  revert hr
  cases runLoop (E.ren σ) (p.rename σ.fwd) n (s.ren σ) <;> simp

/-- A return of the renamed run is a return of the original one. -/
theorem runLoop_ren_returned_inv (σ : Ren) (E : Env) (p : Program) (n : Nat) (s : State)
    {vals : List Val} {m' : Mem} (h : runLoop (E.ren σ) (p.rename σ.fwd) n (s.ren σ) = .returned vals m') :
    ∃ m, runLoop E p n s = .returned vals m ∧ m' = m.ren σ := by
  have hr := runLoop_ren σ E p n s
  rw [h] at hr
  revert hr
  cases runLoop E p n s <;> simp
  rintro rfl rfl
  exact ⟨_, ⟨rfl, rfl⟩, rfl⟩

/-- A trap of the renamed run is a trap of the original one. -/
theorem runLoop_ren_trapped_inv (σ : Ren) (E : Env) (p : Program) (n : Nat) (s : State)
    {c : TrapCode} (h : runLoop (E.ren σ) (p.rename σ.fwd) n (s.ren σ) = .trapped c) :
    runLoop E p n s = .trapped c := by
  have hr := runLoop_ren σ E p n s
  rw [h] at hr
  revert hr
  cases runLoop E p n s <;> simp [eq_comm]

end Clif
