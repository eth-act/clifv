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
  · split
    · simp only [Option.some.injEq, Prod.mk.injEq]
      rintro ⟨-, rfl, -⟩; exact ⟨rfl, rfl⟩
    · simp
  · split
    · simp only [Option.some.injEq, Prod.mk.injEq]
      rintro ⟨-, rfl, -⟩
      exact ⟨Arm.r_of_write_mem_bytes, Arm.write_mem_bytes_program _ _⟩
    · simp
  · exact ispec_world

/-- An LL/SC loop's run ends without error, with the program unchanged, falling through. -/
theorem loopSem_world {F : BitVec 64 → Prop} {ty : CTy} {a : CV} {body : List Line}
    {regs : List Reg} {uses : List CV} {defs : List Reg} {w : Arm.ArmState} {outs : List CV}
    {w' : Arm.ArmState} {c : Ctl} (h : loopSem F ty a body regs uses defs w = some (outs, w', c)) :
    Arm.r .ERR w' = .None ∧ w'.program = w.program ∧ c = .next := by
  unfold loopSem at h
  split at h
  · split at h
    · split at h
      · rename_i t' _ hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h
        exact ⟨hc.1, hc.2, rfl⟩
      · cases h
    · cases h
  · cases h

/-- The LL/SC loops on an error-free world: their runs (`loopSem_world`). -/
theorem csem_loop_world {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst}
    {uses : List CV} {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState} {c : Ctl}
    (hl : (∃ ty op fl a o d s1 s2, i = .atomicRmwLoop ty op fl a o d s1 s2) ∨
      (∃ ty fl a e r d s1, i = .atomicCasLoop ty fl a e r d s1))
    (h : csem F ctx X i uses w = some (outs, w', c)) (herr : Arm.r .ERR w = .None) :
    Arm.r .ERR w' = .None ∧ w'.program = w.program ∧ c = .next := by
  rcases hl with ⟨ty, op, fl, a, o, d, s1, s2, rfl⟩ | ⟨ty, fl, a, e, r, d, s1, rfl⟩
  · simp only [csem, herr, ite_true] at h
    split at h
    · exact loopSem_world h
    · cases h
  · simp only [csem, herr, ite_true] at h
    split at h
    · split at h
      · rename_i outs1 t1 c1 h1
        have hw1 := loopSem_world h1
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl, rfl⟩ := h
          exact ⟨hw1.1, hw1.2.1, rfl⟩
        · have hw2 := loopSem_world h
          exact ⟨hw2.1, hw2.2.1.trans hw1.2.1, hw2.2.2⟩
      · cases h
    · cases h

/-- The LL/SC loops fall through. -/
theorem csem_loop_ctl {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst}
    {uses : List CV} {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState} {c : Ctl}
    (hl : (∃ ty op fl a o d s1 s2, i = .atomicRmwLoop ty op fl a o d s1 s2) ∨
      (∃ ty fl a e r d s1, i = .atomicCasLoop ty fl a e r d s1))
    (h : csem F ctx X i uses w = some (outs, w', c)) : c = .next := by
  by_cases herr : Arm.r .ERR w = .None
  · exact (csem_loop_world hl h herr).2.2
  · rcases hl with ⟨ty, op, fl, a, o, d, s1, s2, rfl⟩ | ⟨ty, fl, a, e, r, d, s1, rfl⟩
    all_goals
      simp only [csem, herr, ite_false] at h
      split at h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.2.symm
        · cases h
      · cases h

theorem csem_next_world' {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst}
    {uses : List CV} {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState}
    (h : csem F ctx X i uses w = some (outs, w', .next)) (hnc : ∀ info, i ≠ .call info)
    (herr : Arm.r .ERR w = .None) :
    Arm.r .ERR w' = .None ∧ w'.program = w.program := by
  by_cases hl : (∃ ty op fl a o d s1 s2, i = .atomicRmwLoop ty op fl a o d s1 s2) ∨
      (∃ ty fl a e r d s1, i = .atomicCasLoop ty fl a e r d s1)
  · obtain ⟨e1, e2, -⟩ := csem_loop_world hl h herr
    exact ⟨e1, e2⟩
  unfold csem at h
  split at h
  · exact absurd rfl (hnc _)
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, and_false] at h; done)
    | (simp only [Option.map_eq_some_iff, Prod.mk.injEq, reduceCtorEq, and_false, false_and,
        exists_false] at h; done)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl, -⟩ := h; exact ⟨herr, rfl⟩)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl, -⟩ := h
       exact ⟨by
         simp only [Arm.write_pstate]
         rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp),
           Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
         exact herr, by simp [Arm.write_pstate, Arm.w_program]⟩)
    | (split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, and_false] at h <;> done)
    | (exfalso; exact hl (.inl ⟨_, _, _, _, _, _, _, _, rfl⟩))
    | (exfalso; exact hl (.inr ⟨_, _, _, _, _, _, _, rfl⟩))
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
