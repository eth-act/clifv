import FV.Isle.Interp

/-!
# Generic lemmas about the ISLE interpreter (any program, any embedding)

The route to rule correctness recommended by the probe (`docs/contracts/backend-proof.md`):
correctness does not need to know *which* rule of a term is selected, only that the rule the
interpreter commits to matched. With `cfg.checkOverlap = false` (the backend's
configuration):

* `selectRule_some`: a committed rule is one of the candidate rules, and its match phase,
  run from the state the selection started in, succeeded with the returned environment (a
  failed attempt restores the state, so every candidate is tried from the same state), with
  a fuel of at least the selection's fuel minus the number of candidates (rule lemmas are
  stated for all large fuels, so no fuel-monotonicity lemma is needed);
* `applyTerm_internal_some`: an internal constructor term that returns a value committed to
  some rule of `p.rulesOf t` whose match succeeded and whose right-hand side evaluated to that
  value; the rule is then appended to the trace;
* `applyTerm_internal_none`: `none` from an internal constructor means that the term is
  `partial` and no rule matched, or that the committed rule's right-hand side returned `none`
  (a partial constructor failed inside it; there is no backtracking into other rules).

**Match inversion.** A successful match phase determines the shape of the matched values:
`matchRule_some_inv`, `matchArgs_cons_inv`, `matchPat_enum_inv` (an enum-variant pattern
matched a value `sem.unData` decodes to that variant), `matchPat_extract_inv` (an extern
extractor pattern matched through the extractor's result). Rule proofs start from "rule `r`
matched" and use these to recover the CLIF instruction (`IselFamily`).

Nothing here depends on the exported program: the lemmas hold for every `p` and `sem`.
-/

namespace Isle.Interp

variable {V σ : Type} {p : Program} {sem : Sem V σ} {cfg : Config}

section Monad
variable {α β : Type}

@[simp] theorem M.run_bind (x : M σ α) (f : α → M σ β) (s : σ × Array RuleId) :
    (x >>= f).run s = (x.run s >>= fun q => (f q.1).run q.2) := rfl
@[simp] theorem M.run_pure (a : α) (s : σ × Array RuleId) :
    (pure a : M σ α).run s = .ok (a, s) := rfl
@[simp] theorem M.run_get (s : σ × Array RuleId) :
    (get : M σ (σ × Array RuleId)).run s = .ok (s, s) := rfl
@[simp] theorem M.run_set (s s' : σ × Array RuleId) :
    (set s' : M σ PUnit).run s = .ok (⟨⟩, s') := rfl
@[simp] theorem M.run_throw (e : Err) (s : σ × Array RuleId) :
    (throw e : M σ α).run s = .error e := rfl

@[simp] theorem M.except_pure {ε : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl
@[simp] theorem M.run_liftM_ok (a : α) (s : σ × Array RuleId) :
    (liftM (Except.ok a : Except Err α) : M σ α).run s = .ok (a, s) := rfl

theorem M.run_fire_pure (r : RuleId) (a : α) (s : σ × Array RuleId) :
    (do fire r; pure a : M σ α).run s = .ok (a, (s.1, s.2.push r)) := rfl

@[simp] theorem M.except_ok_bind {ε : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f : Except ε β) = f a := rfl

theorem except_bind_eq_ok {ε : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

end Monad

/-- `tryRule` either commits (the match phase's result and state) or restores the state. -/
theorem tryRule_run {n : Nat} {r : Rule} {vs : List V} {s : σ × Array RuleId}
    {res : Option (Env V)} {s' : σ × Array RuleId}
    (h : (tryRule p sem cfg (n + 1) r vs).run s = .ok (res, s')) :
    (∃ env, res = some env ∧ (matchRule p sem cfg n r vs).run s = .ok (some env, s')) ∨
    (res = none ∧ s' = s) := by
  rw [tryRule] at h
  simp only [M.except_ok_bind, M.run_bind, M.run_get] at h
  cases hm : (matchRule p sem cfg n r vs).run s with
  | error e => rw [hm] at h; cases h
  | ok q =>
    obtain ⟨m, s1⟩ := q
    rw [hm] at h
    cases m with
    | some env =>
      simp only [M.except_ok_bind, M.run_pure] at h
      injection h with h; injection h with h1 h2
      exact .inl ⟨env, h1.symm, by rw [h2]⟩
    | none =>
      simp only [M.except_ok_bind, M.run_bind, M.run_set, M.run_pure] at h
      injection h with h; injection h with h1 h2
      exact .inr ⟨h1.symm, h2.symm⟩

/-- **The committed rule matched.** With overlap checking off, if rule selection returns
`(r, env)`, then `r` is one of the candidates and its match phase, run from the selection's
start state, returned `env` (and the state selection returns). -/
theorem selectRule_some (hc : cfg.checkOverlap = false) :
    ∀ {n : Nat} {term : Term} {rs : List Rule} {vs : List V} {s s' : σ × Array RuleId}
      {r : Rule} {env : Env V},
      (selectRule p sem cfg n term rs vs).run s = .ok (some (r, env), s') →
      r ∈ rs ∧ ∃ m, n ≤ m + 2 + rs.length ∧ (matchRule p sem cfg m r vs).run s = .ok (some env, s')
  | 0, _, _, _, _, _, _, _, h => by rw [selectRule.eq_1] at h; cases h
  | n + 1, _, [], _, _, _, _, _, h => by rw [selectRule.eq_2] at h; cases h
  | n + 1, term, r' :: rs, vs, s, s', r, env, h => by
    rw [selectRule.eq_3] at h
    simp only [M.run_bind] at h
    cases n with
    | zero => rw [tryRule.eq_1] at h; cases h
    | succ k =>
      cases ht : (tryRule p sem cfg (k + 1) r' vs).run s with
      | error e => rw [ht] at h; cases h
      | ok q =>
        obtain ⟨res, s1⟩ := q
        rw [ht] at h
        simp only [M.except_ok_bind] at h
        rcases tryRule_run ht with ⟨env', hres, hm⟩ | ⟨hres, hs1⟩
        · subst hres
          simp only [hc, Bool.false_eq_true, ↓reduceIte, M.run_pure, Except.ok.injEq,
            Prod.mk.injEq, Option.some.injEq] at h
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
          exact ⟨List.mem_cons_self .., k, by simp, hm⟩
        · subst hres hs1
          obtain ⟨hr, m, hmn, hm⟩ := selectRule_some hc h
          exact ⟨List.mem_cons_of_mem _ hr, m, by simp; omega, hm⟩

/-- Rule selection returning `none` never changes the state (every failed attempt restores
it). -/
theorem selectRule_none :
    ∀ {n : Nat} {term : Term} {rs : List Rule} {vs : List V} {s s' : σ × Array RuleId},
      (selectRule p sem cfg n term rs vs).run s = .ok (none, s') → s' = s
  | 0, _, _, _, _, _, h => by rw [selectRule.eq_1] at h; cases h
  | n + 1, _, [], _, _, _, h => by
    rw [selectRule.eq_2] at h
    simp only [M.run_pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  | n + 1, term, r' :: rs, vs, s, s', h => by
    rw [selectRule.eq_3] at h
    simp only [M.run_bind] at h
    cases n with
    | zero => rw [tryRule.eq_1] at h; cases h
    | succ k =>
      cases ht : (tryRule p sem cfg (k + 1) r' vs).run s with
      | error e => rw [ht] at h; cases h
      | ok q =>
        obtain ⟨res, s1⟩ := q
        rw [ht] at h
        simp only [M.except_ok_bind] at h
        rcases tryRule_run ht with ⟨env', hres, hm⟩ | ⟨hres, hs1⟩
        · subst hres
          cases hco : cfg.checkOverlap
          · simp [hco] at h
          · simp only [hco, ↓reduceIte, M.run_bind] at h
            cases ha : (alsoMatching p sem cfg (k + 1) (splitClass r'.prio rs).1 vs).run s1 with
            | error e => rw [ha] at h; cases h
            | ok q' =>
              rw [ha] at h
              simp only [M.except_ok_bind] at h
              split at h
              · simp at h
              · cases h
        · subst hres hs1
          exact selectRule_none h

/-- `applyTerm` of an internal constructor term, one step: select a rule, evaluate its
right-hand side, fire it. -/
theorem applyTerm_internal_run {n : Nat} {ty : TypeId} {t : TermId} {vs : List V} {term : Term}
    {flags : TermFlags} {ex : Option Extractor}
    (ht : termOf p t = .ok term) (hk : term.kind = .decl flags (some .internal) ex)
    (hm : flags.isMulti = false) (s : σ × Array RuleId) :
    (applyTerm p sem cfg (n + 1) ty t vs).run s =
      ((selectRule p sem cfg n term (p.rulesOf t) vs).run s >>= fun q =>
        (match q.1 with
        | none => if flags.isPartial then pure none else throw (.noRule term.name)
        | some (r, env) => do
          match ← evalExpr p sem cfg n r.rhs env with
          | some v => do fire r.id; pure (some v)
          | none => pure none : M σ (Option V)).run q.2) := by
  rw [applyTerm.eq_2, ht]
  simp only [M.run_bind, M.run_liftM_ok, M.except_ok_bind, hk, hm, Bool.false_eq_true,
    ↓reduceIte]
  rfl

/-- **An internal constructor's value comes from a committed, matched rule.** If `applyTerm`
of the internal constructor `t` returns `some v`, then some rule `r` of `p.rulesOf t` matched
the arguments from the start state (environment `env`, state `s1`), its right-hand side
evaluated from `(env, s1)` to `some v` with state `(st, tr)`, and the final state is that with
`r` appended to the trace. -/
theorem applyTerm_internal_some (hc : cfg.checkOverlap = false) {n : Nat} {ty : TypeId}
    {t : TermId} {vs : List V} {term : Term} {flags : TermFlags} {ex : Option Extractor}
    (ht : termOf p t = .ok term) (hk : term.kind = .decl flags (some .internal) ex)
    (hm : flags.isMulti = false) {s s' : σ × Array RuleId} {v : V}
    (h : (applyTerm p sem cfg (n + 1) ty t vs).run s = .ok (some v, s')) :
    ∃ r ∈ p.rulesOf t, ∃ m env s1 st tr, n ≤ m + 2 + (p.rulesOf t).length ∧
      (matchRule p sem cfg m r vs).run s = .ok (some env, s1) ∧
      (evalExpr p sem cfg n r.rhs env).run s1 = .ok (some v, (st, tr)) ∧
      s' = (st, tr.push r.id) := by
  rw [applyTerm_internal_run ht hk hm] at h
  cases hs : (selectRule p sem cfg n term (p.rulesOf t) vs).run s with
  | error e => rw [hs] at h; cases h
  | ok q =>
    obtain ⟨sel, s1⟩ := q
    rw [hs] at h
    simp only [M.except_ok_bind] at h
    cases sel with
    | none =>
      simp only at h
      split at h
      · simp at h
      · cases h
    | some re =>
      obtain ⟨r, env⟩ := re
      obtain ⟨hr, m, hmn, hmatch⟩ := selectRule_some hc hs
      simp only [M.run_bind] at h
      cases he : (evalExpr p sem cfg n r.rhs env).run s1 with
      | error e => rw [he] at h; cases h
      | ok q =>
        obtain ⟨ev, st, tr⟩ := q
        rw [he] at h
        simp only [M.except_ok_bind] at h
        cases ev with
        | none => simp at h
        | some w =>
          simp only [M.run_fire_pure, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨r, hr, m, env, s1, st, tr, hmn, hmatch, he, rfl⟩

/-- **Partial-constructor failure.** If `applyTerm` of the internal constructor `t` returns
`none`, then either no rule matched (the term is `partial`, and the state is unchanged) or a
rule matched and its right-hand side returned `none` (a partial constructor failed inside it;
no other rule is tried). -/
theorem applyTerm_internal_none (hc : cfg.checkOverlap = false) {n : Nat} {ty : TypeId}
    {t : TermId} {vs : List V} {term : Term} {flags : TermFlags} {ex : Option Extractor}
    (ht : termOf p t = .ok term) (hk : term.kind = .decl flags (some .internal) ex)
    (hm : flags.isMulti = false) {s s' : σ × Array RuleId}
    (h : (applyTerm p sem cfg (n + 1) ty t vs).run s = .ok (none, s')) :
    (flags.isPartial = true ∧ s' = s) ∨
    ∃ r ∈ p.rulesOf t, ∃ m env s1,
      (matchRule p sem cfg m r vs).run s = .ok (some env, s1) ∧
      (evalExpr p sem cfg n r.rhs env).run s1 = .ok (none, s') := by
  rw [applyTerm_internal_run ht hk hm] at h
  cases hs : (selectRule p sem cfg n term (p.rulesOf t) vs).run s with
  | error e => rw [hs] at h; cases h
  | ok q =>
    obtain ⟨sel, s1⟩ := q
    rw [hs] at h
    simp only [M.except_ok_bind] at h
    cases sel with
    | none =>
      have := selectRule_none hs
      subst this
      simp only at h
      split at h
      · simp only [M.run_pure, Except.ok.injEq, Prod.mk.injEq] at h
        exact .inl ⟨by assumption, h.2.symm⟩
      · cases h
    | some re =>
      obtain ⟨r, env⟩ := re
      obtain ⟨hr, m, -, hmatch⟩ := selectRule_some hc hs
      simp only [M.run_bind] at h
      cases he : (evalExpr p sem cfg n r.rhs env).run s1 with
      | error e => rw [he] at h; cases h
      | ok q =>
        obtain ⟨ev, s2⟩ := q
        rw [he] at h
        simp only [M.except_ok_bind] at h
        cases ev with
        | none =>
          simp only [M.run_pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact .inr ⟨r, hr, m, env, s1, hmatch, he⟩
        | some w =>
          simp only [M.run_fire_pure, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq,
            false_and] at h

/-! ## Match inversion -/

/-- A successful match phase: the argument patterns matched (from the empty environment), then
the if-lets. -/
theorem matchRule_some_inv {m : Nat} {r : Rule} {vs : List V} {s s1 : σ × Array RuleId}
    {env : Env V} (h : (matchRule p sem cfg (m + 1) r vs).run s = .ok (some env, s1)) :
    ∃ env0, matchArgs p sem s.1 r.args vs (Array.replicate r.vars.length none) = .ok (some env0) ∧
      (matchIfLets p sem cfg m r.iflets env0).run s = .ok (some env, s1) := by
  rw [matchRule.eq_2] at h
  simp only [M.run_bind, M.run_get, M.except_ok_bind] at h
  cases ha : matchArgs p sem s.1 r.args vs (Array.replicate r.vars.length none) with
  | error e =>
    rw [ha] at h; cases h
  | ok o =>
    rw [ha] at h
    cases o with
    | none =>
      simp only [M.run_liftM_ok, M.except_ok_bind, M.run_pure] at h
      cases h
    | some env0 =>
      simp only [M.run_liftM_ok, M.except_ok_bind] at h
      exact ⟨env0, rfl, h⟩

theorem matchArgs_cons_inv {st : σ} {q : Pattern} {qs : List Pattern} {w : V} {ws : List V}
    {env env' : Env V} (h : matchArgs p sem st (q :: qs) (w :: ws) env = .ok (some env')) :
    ∃ env1, matchPat p sem st q w env = .ok (some env1) ∧
      matchArgs p sem st qs ws env1 = .ok (some env') := by
  rw [matchArgs.eq_2] at h
  cases hq : matchPat p sem st q w env with
  | error e => rw [hq] at h; cases h
  | ok o =>
    rw [hq] at h
    cases o with
    | none => cases h
    | some env1 => exact ⟨env1, rfl, h⟩

/-- An enum-variant pattern matched: the value decodes to that variant, and the fields matched. -/
theorem matchPat_enum_inv {st : σ} {ty : TypeId} {t : TermId} {args : List Pattern} {v : V}
    {env env' : Env V} {term : Term} {k : Nat} (ht : termOf p t = .ok term)
    (hk : term.kind = .enumVariant k)
    (h : matchPat p sem st (.term ty t args) v env = .ok (some env')) :
    ∃ fs, sem.unData ty v = some (k, fs) ∧ matchArgs p sem st args fs env = .ok (some env') := by
  rw [matchPat.eq_8, ht] at h
  simp only [M.except_ok_bind, hk] at h
  cases hu : sem.unData ty v with
  | none => rw [hu] at h; cases h
  | some q =>
    obtain ⟨k', fs⟩ := q
    rw [hu] at h
    simp only at h
    by_cases hkk : k = k'
    · subst hkk
      simp only [beq_self_eq_true, ↓reduceIte] at h
      exact ⟨fs, rfl, h⟩
    · simp [hkk] at h

/-- An extern-extractor pattern matched: the extractor succeeded, and its results matched. -/
theorem matchPat_extract_inv {st : σ} {ty : TypeId} {t : TermId} {args : List Pattern} {v : V}
    {env env' : Env V} {term : Term} {flags : TermFlags} {c : Option Ctor} {fn : String}
    {inf : Bool} (ht : termOf p t = .ok term)
    (hk : term.kind = .decl flags c (some (.external fn inf))) (hm : flags.isMulti = false)
    (h : matchPat p sem st (.term ty t args) v env = .ok (some env')) :
    ∃ fs, sem.extract term v st = .ok fs ∧ matchArgs p sem st args fs env = .ok (some env') := by
  rw [matchPat.eq_8, ht] at h
  simp only [M.except_ok_bind, hk, hm, Bool.false_eq_true, ↓reduceIte] at h
  cases he : sem.extract term v st with
  | ok fs => rw [he] at h; exact ⟨fs, rfl, h⟩
  | fail =>
    rw [he] at h
    simp only at h
    split at h <;> cases h
  | unmodeled w => rw [he] at h; cases h

theorem matchPat_bind_inv {st : σ} {ty : TypeId} {x : VarId} {sub : Pattern} {v : V}
    {env env' : Env V} (h : matchPat p sem st (.bind ty x sub) v env = .ok (some env')) :
    x < env.size ∧ matchPat p sem st sub v (env.set! x (some v)) = .ok (some env') := by
  rw [matchPat.eq_1] at h
  split at h
  · exact ⟨by assumption, h⟩
  · cases h


end Isle.Interp
