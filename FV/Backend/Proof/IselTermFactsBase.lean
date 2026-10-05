import FV.Backend.Proof.IselCtl
import FV.Backend.Proof.IselCtlTry

/-!
# Completeness of `lowerCheck`: the rule a driver call committed to

`runTerm_lower_rule`, `runTerm_lower_branch_rule`: a successful `lower` / `lower_branch` call of
the driver (`runTerm`, fuel 10⁶) committed to one rule of the term, the rules before it having
failed to match, and that rule's right-hand side returned the call's result (as
`lowerInstOk_runTerm` / `branchOk_runTerm` unfold it, without a semantic conclusion).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- The VCode instruction specification refines itself (any semantic parameter of the rule
lemmas can be instantiated by it). -/
theorem refines_ispec : Refines (fun _ => True) ispec :=
  fun _ _ _ _ w' _ h => ⟨w', h, SameWorld.refl _ _⟩

set_option maxRecDepth 20000 in
/-- A successful `lower` call committed to a rule of `lower` (the rules before it failed to
match) whose right-hand side returned. -/
theorem runTerm_lower_rule {ctx : Ctx} {vs : List V} {st : LState} {out : V} {st' : LState}
    {tr : List RuleId} (h : runTerm ctx "lower" vs st = .ok (some out, st', tr)) :
    ∃ r ∈ program.rulesOf TId.lower, ∃ (m n : Nat) (env' : Interp.Env V)
      (s1 : LState × Array RuleId) (tr2 : Array RuleId), 1000 ≤ m ∧ 1000 ≤ n ∧
      (∀ pre post, program.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
        ∃ s', (matchRule program (sem ctx) {} m' r' vs).run (st, #[]) = .ok (none, s')) ∧
      (matchRule program (sem ctx) {} m r vs).run (st, #[]) = .ok (some env', s1) ∧
      (evalExpr program (sem ctx) {} n r.rhs env').run s1 = .ok (some out, (st', tr2)) := by
  unfold runTerm Interp.run at h
  rw [program_termByName_lower] at h
  dsimp only at h
  cases ha : (applyTerm program (sem ctx) {} 1000000 T.lower.ret T.lower.id vs).run (st, #[]) with
  | error e => rw [ha] at h; cases h
  | ok q =>
    obtain ⟨v, st2, tr2⟩ := q
    rw [ha] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    injection h with h
    injection h with h1 h2
    subst h1
    injection h2 with h2 _
    subst h2
    have hlen : (program.rulesOf 686).length ≤ 1000 := by
      rw [data_program.r686]; decide
    obtain ⟨r, pre0, post0, hsplit, hpre0, m, env', s1, st3, tr3, hmn, hmatch, heval, hs⟩ :=
      applyTerm_internal_some_first (n := 999999) (cfg := {}) rfl data_program.t686 term_686_kind
        rfl ha
    simp only [Prod.mk.injEq] at hs
    obtain ⟨rfl, -⟩ := hs
    refine ⟨r, ?_, m, 999999, env', s1, tr3, by omega, by omega, ?_, hmatch, heval⟩
    · change r ∈ program.rulesOf 686; rw [hsplit]; simp
    · intro pre post hsp r' hr'
      have hnd : (pre0 ++ r :: post0).Nodup := hsplit ▸ lower_rules_nodup data_program
      have hpre := prefix_unique_of_nodup hnd (hsplit.symm.trans hsp)
      subst hpre
      obtain ⟨m', hm', s', h'⟩ := hpre0 r' hr'
      exact ⟨m', by omega, s', h'⟩

set_option maxRecDepth 20000 in
/-- A successful `lower_branch` call committed to a rule of `lower_branch` (the rules before it
failed to match) whose right-hand side returned. -/
theorem runTerm_lower_branch_rule {ctx : Ctx} {vs : List V} {st : LState} {out : V}
    {st' : LState} {tr : List RuleId}
    (h : runTerm ctx "lower_branch" vs st = .ok (some out, st', tr)) :
    ∃ r ∈ program.rulesOf TId.lower_branch, ∃ (m n : Nat) (env' : Interp.Env V)
      (s1 : LState × Array RuleId) (tr2 : Array RuleId), 1000 ≤ m ∧ 1000 ≤ n ∧
      (∀ pre post, program.rulesOf TId.lower_branch = pre ++ r :: post → ∀ r' ∈ pre,
        ∃ m', 1000 ≤ m' ∧
          ∃ s', (matchRule program (sem ctx) {} m' r' vs).run (st, #[]) = .ok (none, s')) ∧
      (matchRule program (sem ctx) {} m r vs).run (st, #[]) = .ok (some env', s1) ∧
      (evalExpr program (sem ctx) {} n r.rhs env').run s1 = .ok (some out, (st', tr2)) := by
  unfold runTerm Interp.run at h
  rw [program_termByName_lower_branch] at h
  dsimp only at h
  cases ha : (applyTerm program (sem ctx) {} 1000000 T.lower_branch.ret T.lower_branch.id vs).run
      (st, #[]) with
  | error e => rw [ha] at h; cases h
  | ok q =>
    obtain ⟨v, st2, tr2⟩ := q
    rw [ha] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    injection h with h
    injection h with h1 h2
    subst h1
    injection h2 with h2 _
    subst h2
    have hlen : (program.rulesOf 687).length ≤ 1000 := by
      rw [data_program.r687]; decide
    obtain ⟨r, pre0, post0, hsplit, hpre0, m, env', s1, st3, tr3, hmn, hmatch, heval, hs⟩ :=
      applyTerm_internal_some_first (n := 999999) (cfg := {}) rfl data_program.t687 term_687_kind
        rfl ha
    simp only [Prod.mk.injEq] at hs
    obtain ⟨rfl, -⟩ := hs
    refine ⟨r, ?_, m, 999999, env', s1, tr3, by omega, by omega, ?_, hmatch, heval⟩
    · change r ∈ program.rulesOf 687; rw [hsplit]; simp
    · intro pre post hsp r' hr'
      have hnd : (pre0 ++ r :: post0).Nodup := hsplit ▸ lower_branch_rules_nodup data_program
      have hpre := prefix_unique_of_nodup hnd (hsplit.symm.trans hsp)
      subst hpre
      obtain ⟨m', hm', s', h'⟩ := hpre0 r' hr'
      exact ⟨m', by omega, s', h'⟩

end Backend.Proof
