import FV.Backend.Proof.RegallocCSem

/-!
# Worlds of `csem` steps (M6 proof)

`ispec_world`: an `ispec` step keeps the error field and the program (it writes at most the
flags). `csem_next_world'`: a `next` step of `csem` other than a call keeps the program and an
error-free world (straight-line forms by `straightSem_some`, `ispec` fallback by
`ispec_world`).
-/

namespace Backend.Proof

open Backend

theorem write_pstate_err (p : Arm.PState) (w : Arm.ArmState) :
    Arm.r .ERR (Arm.write_pstate p w) = Arm.r .ERR w ∧ (Arm.write_pstate p w).program = w.program := by
  simp [Arm.write_pstate, Arm.r_of_w_different, Arm.w_program]

set_option maxHeartbeats 4000000 in
theorem ispec_world {i : MInst} {uses : List CV} {w : Arm.ArmState} {outs : List CV}
    {w' : Arm.ArmState} {ctl : Ctl} (h : ispec i uses w = some (outs, w', ctl)) :
    Arm.r .ERR w' = Arm.r .ERR w ∧ w'.program = w.program := by
  revert h
  unfold ispec
  split
  all_goals (repeat' split)
  all_goals intro h
  all_goals simp only [Option.map_eq_some_iff, Option.some.injEq, Prod.mk.injEq, reduceCtorEq,
    false_and, and_false] at h
  all_goals first
    | (obtain ⟨-, rfl, -⟩ := h; exact ⟨rfl, rfl⟩)
    | (obtain ⟨-, rfl, -⟩ := h; exact write_pstate_err _ _)
    | (obtain ⟨_, -, -, rfl, -⟩ := h; exact ⟨rfl, rfl⟩)

theorem mspec_world {sb : Nat} {i : MInst} {uses : List CV} {w : Arm.ArmState} {outs : List CV}
    {w' : Arm.ArmState} {ctl : Ctl} (h : mspec sb i uses w = some (outs, w', ctl)) :
    Arm.r .ERR w' = Arm.r .ERR w ∧ w'.program = w.program := by
  revert h
  unfold mspec
  split
  · split
    · simp
    · simp only [Option.map_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
      rintro ⟨_, -, -, rfl, -⟩; exact ⟨rfl, rfl⟩
  · split
    · simp
    · simp only [Option.map_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
      rintro ⟨_, -, -, rfl, -⟩
      exact ⟨Arm.r_of_write_mem_bytes, Arm.write_mem_bytes_program _ _⟩
  · simp only [Option.some.injEq, Prod.mk.injEq]
    rintro ⟨-, rfl, -⟩; exact ⟨rfl, rfl⟩
  · exact ispec_world

theorem csem_next_world' {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst}
    {uses : List CV} {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState}
    (h : csem F ctx X i uses w = some (outs, w', .next)) (hnc : ∀ info, i ≠ .call info)
    (herr : Arm.r .ERR w = .None) :
    Arm.r .ERR w' = .None ∧ w'.program = w.program := by
  unfold csem at h
  split at h
  · exact absurd rfl (hnc _)
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, and_false] at h; done)
    | (simp only [Option.map_eq_some_iff, Prod.mk.injEq, reduceCtorEq, and_false, false_and,
        exists_false] at h; done)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl, -⟩ := h; exact ⟨herr, rfl⟩)
    | (split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, and_false] at h <;> done)
    | skip
  all_goals first
    | (split at h
       · exact (straightSem_some h).2
       · obtain ⟨e1, e2⟩ := mspec_world h; exact ⟨e1.trans herr, e2⟩)
    | (split at h
       · split at h
         · simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, and_false] at h
         · simp only at h
           split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, and_false, reduceCtorEq] at h
       · cases h)

end Backend.Proof
