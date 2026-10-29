module

public import FV.Concurrency.ProgramWitness
public import FV.Concurrency.ProgramE2EF

@[expose] public section

/-!
# Non-vacuity of `program_correctF` and `program_correct_rust`

The two returning threads of `ProgramWitness` (`ret_correct`): race-freedom over every
`ConsistentF` execution (`raceFreeProgF_of_raceFreeProg`), and Rust race-freedom over every
C++20-consistent execution with cg_clif's orderings read back from the CLIF kinds
(`SKind.liftSC`: every atomic and fence `seq_cst`).
-/

namespace Concurrency.ProgWitness

open Rel Prog ClifThread ProgE2E

/-- **Rust race-freedom of the program**: its threads have no memory events. -/
theorem ret_rustRaceFree (M0 : Bytes) :
    RustRaceFree env0 p0 2 s0 M0 (fun P e => (kindC P e).liftSC) := by
  refine ⟨fun P e => SKind.strength_liftSC _, ?_⟩
  intro P locs rf co rmw _ hs0 hruns _ _ _ _ _ a _ ha _ hconf _
  exact absurd (ret_dirF hs0 hruns a ha) hconf.2.2.1

/-- **Non-vacuity of `program_correctF`**: the two returning threads. -/
theorem ret_correctF : ∃ ts B, MTRun env0 p0 (s0, fun _ => none) (ts, B) ∧
    StripEq ts (fun i => PC.st i (if i < PC.n then (PC.tr i).length else 0)) ∧
    (∀ i < PC.n, Obs i (PA.st i (PA.tr i).length) (PC.st i (PC.tr i).length)) := by
  obtain ⟨-, ts, B, h1, h2, -, h3⟩ := program_correctF realizes wfA
    (raceFreeProgF_of_raceFreeProg (ret_raceFree _))
    (fun i hi j hj => absurd hj (Nat.not_lt_zero _)) consA (fun _ _ h => h.elim)
    (fun a _ ha => absurd (PA_dir a) ha) (fun _ _ h => h.elim) runsC rfl (fun _ => rfl)
  exact ⟨ts, B, h1, h2, h3⟩

/-- **Non-vacuity of `program_correct_rust`** (and `raceFreeProgF_of_rust`): the two returning
threads. -/
theorem ret_correct_rust : ∃ ts B, MTRun env0 p0 (s0, fun _ => none) (ts, B) ∧
    StripEq ts (fun i => PC.st i (if i < PC.n then (PC.tr i).length else 0)) ∧
    (∀ i < PC.n, Obs i (PA.st i (PA.tr i).length) (PC.st i (PC.tr i).length)) := by
  obtain ⟨-, ts, B, h1, h2, -, h3⟩ := program_correct_rust realizes wfA (ret_rustRaceFree _)
    (fun i hi j hj => absurd hj (Nat.not_lt_zero _)) consA (fun _ _ h => h.elim)
    (fun a _ ha => absurd (PA_dir a) ha) (fun _ _ h => h.elim) runsC rfl (fun _ => rfl)
  exact ⟨ts, B, h1, h2, h3⟩

end Concurrency.ProgWitness
