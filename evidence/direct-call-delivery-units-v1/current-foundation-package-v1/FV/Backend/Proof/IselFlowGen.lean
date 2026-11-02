import FV.Backend.Proof.IselGeneric

/-!
# Generic invariants of ISLE runs

For any program and embedding, with overlap checking off:

* `presAt`: a preorder `R` on embedding states that every extern constructor call respects
  (`sem.ctor … st = .ok (v, st') → R st st'`) relates the start and end states of every
  interpreter function (a failed match attempt restores a state the run started from).
-/

namespace Isle.Interp

variable {V σ : Type} {p : Program} {sem : Sem V σ} {cfg : Config}

section Run
variable {α β : Type}

theorem bind_ok {x : M σ α} {f : α → M σ β} {s : σ × Array RuleId} {b : β × (σ × Array RuleId)}
    (h : (x >>= f).run s = .ok b) : ∃ a s1, x.run s = .ok (a, s1) ∧ (f a).run s1 = .ok b := by
  rw [M.run_bind] at h
  obtain ⟨⟨a, s1⟩, h1, h2⟩ := except_bind_eq_ok h
  exact ⟨a, s1, h1, h2⟩

theorem pure_ok {a : α} {s : σ × Array RuleId} {b : α × (σ × Array RuleId)}
    (h : (pure a : M σ α).run s = .ok b) : b = (a, s) := by
  rw [M.run_pure] at h; injection h with h; exact h.symm

theorem throw_ok {e : Err} {s : σ × Array RuleId} {b : α × (σ × Array RuleId)}
    (h : (throw e : M σ α).run s = .ok b) : False := by
  rw [M.run_throw] at h; cases h

theorem liftM_ok {e : Except Err α} {s : σ × Array RuleId} {b : α × (σ × Array RuleId)}
    (h : (liftM e : M σ α).run s = .ok b) : ∃ a, e = .ok a ∧ b = (a, s) := by
  cases e with
  | error e => cases h
  | ok a => rw [M.run_liftM_ok] at h; injection h with h; exact ⟨a, rfl, h.symm⟩

theorem get_ok {s : σ × Array RuleId} {b : (σ × Array RuleId) × (σ × Array RuleId)}
    (h : (get : M σ (σ × Array RuleId)).run s = .ok b) : b = (s, s) := by
  rw [M.run_get] at h; injection h with h; exact h.symm

theorem set_ok {s s' : σ × Array RuleId} {b : PUnit × (σ × Array RuleId)}
    (h : (set s' : M σ PUnit).run s = .ok b) : b = (⟨⟩, s') := by
  rw [M.run_set] at h; injection h with h; exact h.symm

theorem fire_ok {r : RuleId} {s : σ × Array RuleId} {b : Unit × (σ × Array RuleId)}
    (h : (fire r : M σ Unit).run s = .ok b) : b.2.1 = s.1 := by
  obtain ⟨st, tr⟩ := s
  change Except.ok ((), (st, tr.push r)) = _ at h
  injection h with h; rw [← h]

end Run

/-! ## State preservation -/

section Pres
variable (p sem cfg)
variable (R : σ → σ → Prop)

/-- `R` relates the start and end state of every run of every interpreter function at fuel
`n`. -/
structure PresAt (n : Nat) : Prop where
  expr : ∀ e env s tr r s' tr', (evalExpr p sem cfg n e env).run (s, tr) = .ok (r, (s', tr')) →
    R s s'
  args : ∀ es env s tr r s' tr', (evalArgs p sem cfg n es env).run (s, tr) = .ok (r, (s', tr')) →
    R s s'
  binds : ∀ bs env s tr r s' tr', (evalBinds p sem cfg n bs env).run (s, tr) =
    .ok (r, (s', tr')) → R s s'
  apply : ∀ ty t vs s tr r s' tr', (applyTerm p sem cfg n ty t vs).run (s, tr) =
    .ok (r, (s', tr')) → R s s'
  mrule : ∀ rl vs s tr r s' tr', (matchRule p sem cfg n rl vs).run (s, tr) =
    .ok (r, (s', tr')) → R s s'
  iflets : ∀ ils env s tr r s' tr', (matchIfLets p sem cfg n ils env).run (s, tr) =
    .ok (r, (s', tr')) → R s s'
  tryr : ∀ rl vs s tr r s' tr', (tryRule p sem cfg n rl vs).run (s, tr) =
    .ok (r, (s', tr')) → R s s'
  also : ∀ rs vs s tr r s' tr', (alsoMatching p sem cfg n rs vs).run (s, tr) =
    .ok (r, (s', tr')) → R s s'
  select : ∀ term rs vs s tr r s' tr', (selectRule p sem cfg n term rs vs).run (s, tr) =
    .ok (r, (s', tr')) → R s s'

variable {p sem cfg R}

theorem presAt (hrefl : ∀ s, R s s) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hctor : ∀ term vs s v s', sem.ctor term vs s = .ok (v, s') → R s s') :
    ∀ n, PresAt p sem cfg R n := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rename_i h <;>
      first
      | (rw [evalExpr.eq_1] at h; exact (throw_ok h).elim)
      | (rw [evalArgs.eq_1] at h; exact (throw_ok h).elim)
      | (rw [evalBinds.eq_1] at h; exact (throw_ok h).elim)
      | (rw [applyTerm.eq_1] at h; exact (throw_ok h).elim)
      | (rw [matchRule.eq_1] at h; exact (throw_ok h).elim)
      | (rw [matchIfLets.eq_1] at h; exact (throw_ok h).elim)
      | (rw [tryRule.eq_1] at h; exact (throw_ok h).elim)
      | (rw [alsoMatching.eq_1] at h; exact (throw_ok h).elim)
      | (rw [selectRule.eq_1] at h; exact (throw_ok h).elim)
  | succ n ih =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- evalExpr
      intro e env s tr r s' tr' h
      cases e with
      | var ty x =>
        rw [evalExpr.eq_2] at h
        split at h
        · cases pure_ok h; exact hrefl s
        · exact (throw_ok h).elim
      | constBool ty b => rw [evalExpr.eq_3] at h; cases pure_ok h; exact hrefl s
      | constInt ty i => rw [evalExpr.eq_4] at h; cases pure_ok h; exact hrefl s
      | constPrim ty nm =>
        rw [evalExpr.eq_5] at h
        split at h
        · cases pure_ok h; exact hrefl s
        · exact (throw_ok h).elim
      | «let» ty bs body =>
        rw [evalExpr.eq_6] at h
        obtain ⟨a, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
        have r1 := ih.binds _ _ _ _ _ _ _ h1
        cases a with
        | some env' => exact htrans _ _ _ r1 (ih.expr _ _ _ _ _ _ _ h2)
        | none => cases pure_ok h2; exact r1
      | term ty t args =>
        rw [evalExpr.eq_7] at h
        obtain ⟨a, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
        have r1 := ih.args _ _ _ _ _ _ _ h1
        cases a with
        | some vs => exact htrans _ _ _ r1 (ih.apply _ _ _ _ _ _ _ _ h2)
        | none => cases pure_ok h2; exact r1
    · -- evalArgs
      intro es env s tr r s' tr' h
      cases es with
      | nil => rw [evalArgs.eq_2] at h; cases pure_ok h; exact hrefl s
      | cons e es =>
        rw [evalArgs.eq_3] at h
        obtain ⟨a, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
        have r1 := ih.expr _ _ _ _ _ _ _ h1
        cases a with
        | none => cases pure_ok h2; exact r1
        | some v =>
          obtain ⟨b, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
          have r2 := ih.args _ _ _ _ _ _ _ h3
          cases b with
          | some vs => cases pure_ok h4; exact htrans _ _ _ r1 r2
          | none => cases pure_ok h4; exact htrans _ _ _ r1 r2
    · -- evalBinds
      intro bs env s tr r s' tr' h
      cases bs with
      | nil => rw [evalBinds.eq_2] at h; cases pure_ok h; exact hrefl s
      | cons b bs =>
        obtain ⟨x, ty, e⟩ := b
        rw [evalBinds.eq_3] at h
        obtain ⟨a, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
        have r1 := ih.expr _ _ _ _ _ _ _ h1
        cases a with
        | none => cases pure_ok h2; exact r1
        | some v =>
          simp only at h2
          split at h2
          · exact htrans _ _ _ r1 (ih.binds _ _ _ _ _ _ _ h2)
          · exact (throw_ok h2).elim
    · -- applyTerm
      intro ty t vs s tr r s' tr' h
      rw [applyTerm.eq_2] at h
      obtain ⟨term, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
      obtain ⟨_, -, he⟩ := liftM_ok h1
      cases he
      split at h2
      · cases pure_ok h2; exact hrefl s
      · cases pure_ok h2; exact hrefl s
      · split at h2
        · exact (throw_ok h2).elim
        · obtain ⟨g, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
          cases get_ok h3
          simp only at h4
          split at h4
          · rename_i v st' hc
            obtain ⟨u, ⟨s3, tr3⟩, h5, h6⟩ := bind_ok h4
            cases set_ok h5
            cases pure_ok h6
            exact hctor _ _ _ _ _ hc
          · split at h4
            · cases pure_ok h4; exact hrefl s
            · exact (throw_ok h4).elim
          · exact (throw_ok h4).elim
      · split at h2
        · exact (throw_ok h2).elim
        · obtain ⟨sel, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
          have r1 := ih.select _ _ _ _ _ _ _ _ h3
          split at h4
          · split at h4
            · cases pure_ok h4; exact r1
            · exact (throw_ok h4).elim
          · obtain ⟨ev, ⟨s3, tr3⟩, h5, h6⟩ := bind_ok h4
            have r2 := ih.expr _ _ _ _ _ _ _ h5
            split at h6
            · obtain ⟨u, ⟨s4, tr4⟩, h7, h8⟩ := bind_ok h6
              have hf := fire_ok h7
              cases pure_ok h8
              simp only at hf
              subst hf
              exact htrans _ _ _ r1 r2
            · cases pure_ok h6; exact htrans _ _ _ r1 r2
      · exact (throw_ok h2).elim
    · -- matchRule
      intro rl vs s tr r s' tr' h
      rw [matchRule.eq_2] at h
      obtain ⟨g, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
      cases get_ok h1
      simp only at h2
      obtain ⟨m, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
      obtain ⟨_, -, he⟩ := liftM_ok h3
      cases he
      cases m with
      | none => cases pure_ok h4; exact hrefl s
      | some env => exact ih.iflets _ _ _ _ _ _ _ h4
    · -- matchIfLets
      intro ils env s tr r s' tr' h
      cases ils with
      | nil => rw [matchIfLets.eq_2] at h; cases pure_ok h; exact hrefl s
      | cons il ils =>
        rw [matchIfLets.eq_3] at h
        obtain ⟨a, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
        have r1 := ih.expr _ _ _ _ _ _ _ h1
        cases a with
        | none => cases pure_ok h2; exact r1
        | some v =>
          obtain ⟨g, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
          cases get_ok h3
          simp only at h4
          obtain ⟨m, ⟨s3, tr3⟩, h5, h6⟩ := bind_ok h4
          obtain ⟨_, -, he⟩ := liftM_ok h5
          cases he
          cases m with
          | none => cases pure_ok h6; exact r1
          | some env' => exact htrans _ _ _ r1 (ih.iflets _ _ _ _ _ _ _ h6)
    · -- tryRule
      intro rl vs s tr r s' tr' h
      cases n with
      | zero =>
        rw [tryRule.eq_2] at h
        obtain ⟨g, s1, h1, h2⟩ := bind_ok h
        cases get_ok h1
        obtain ⟨m, s2, h3, -⟩ := bind_ok h2
        rw [matchRule.eq_1] at h3
        exact (throw_ok h3).elim
      | succ k =>
        rcases tryRule_run h with ⟨env, -, hm⟩ | ⟨-, hs⟩
        · exact ih.mrule _ _ _ _ _ _ _ hm
        · cases hs; exact hrefl s
    · -- alsoMatching
      intro rs vs s tr r s' tr' h
      cases rs with
      | nil => rw [alsoMatching.eq_2] at h; cases pure_ok h; exact hrefl s
      | cons rl rs =>
        rw [alsoMatching.eq_3] at h
        obtain ⟨g, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
        cases get_ok h1
        obtain ⟨m, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
        obtain ⟨u, ⟨s3, tr3⟩, h5, h6⟩ := bind_ok h4
        cases set_ok h5
        obtain ⟨rest, ⟨s4, tr4⟩, h7, h8⟩ := bind_ok h6
        cases pure_ok h8
        exact ih.also _ _ _ _ _ _ _ h7
    · -- selectRule
      intro term rs vs s tr r s' tr' h
      cases rs with
      | nil => rw [selectRule.eq_2] at h; cases pure_ok h; exact hrefl s
      | cons rl rs =>
        rw [selectRule.eq_3] at h
        obtain ⟨a, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
        have r1 := ih.tryr _ _ _ _ _ _ _ h1
        cases a with
        | none => exact htrans _ _ _ r1 (ih.select _ _ _ _ _ _ _ _ h2)
        | some env =>
          simp only at h2
          split at h2
          · obtain ⟨o, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
            have r2 := ih.also _ _ _ _ _ _ _ h3
            split at h4
            · cases pure_ok h4; exact htrans _ _ _ r1 r2
            · exact (throw_ok h4).elim
          · cases pure_ok h2; exact r1

end Pres

end Isle.Interp
