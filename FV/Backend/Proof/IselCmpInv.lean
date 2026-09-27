import FV.Backend.Proof.IselGeneric

/-!
# Inverse evaluation of the ISLE interpreter (flags/select/div family)

The foundation's `isel_eval` evaluates rules *forward*: it needs every extractor result and
every selected rule to be computable from hypotheses. For terms whose rule choice depends on
the DFG (`emit_icmp`'s constant look-throughs, `is_nonzero`, `is_nonzero_cmp`) and for
right-hand sides that call such terms, we reason *backwards* from "this evaluation returned
`some v`": `iff` lemmas that rewrite a successful match / evaluation into the facts it implies,
used as `simp only … at h`. Internal constructor calls are left as `ApplyInternal`
hypotheses, to be discharged by the callee's contract lemma, so a callee is analysed once.

All lemmas are generic (any program `p`, any embedding `sem`); fuel appears only as `n + 1`.
-/

namespace Isle.Interp

variable {V σ : Type} {p : Program} {sem : Sem V σ} {cfg : Config}

/-! ## Match phase -/

theorem matchRule_iff {m : Nat} {r : Rule} {vs : List V} {s s1 : σ × Array RuleId}
    {env : Env V} :
    (matchRule p sem cfg (m + 1) r vs).run s = .ok (some env, s1) ↔
      ∃ env0, matchArgs p sem s.1 r.args vs (Array.replicate r.vars.length none) = .ok (some env0) ∧
        (matchIfLets p sem cfg m r.iflets env0).run s = .ok (some env, s1) := by
  rw [matchRule.eq_2]
  simp only [M.run_bind, M.run_get, M.except_ok_bind]
  cases ha : matchArgs p sem s.1 r.args vs (Array.replicate r.vars.length none) with
  | error e => simp [bind, Except.bind]
  | ok o =>
    cases o with
    | none => simp [liftM, monadLift, MonadLift.monadLift, StateT.lift, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, StateT.run]
    | some env0 =>
      simp only [M.run_liftM_ok, M.except_ok_bind, Except.ok.injEq, Option.some.injEq, exists_eq_left']

theorem matchArgs_nil_iff {st : σ} {ws : List V} {env env' : Env V} :
    matchArgs p sem st [] ws env = .ok (some env') ↔ ws = [] ∧ env' = env := by
  cases ws with
  | nil => rw [matchArgs.eq_1]; simp [pure, Except.pure, eq_comm]
  | cons w ws => rw [matchArgs.eq_3] <;> simp [throw, throwThe, MonadExceptOf.throw]

theorem matchArgs_cons_iff {st : σ} {q : Pattern} {qs : List Pattern} {ws : List V}
    {env env' : Env V} :
    matchArgs p sem st (q :: qs) ws env = .ok (some env') ↔
      ∃ w ws', ws = w :: ws' ∧ ∃ env1, matchPat p sem st q w env = .ok (some env1) ∧
        matchArgs p sem st qs ws' env1 = .ok (some env') := by
  cases ws with
  | nil => rw [matchArgs.eq_3] <;> simp [throw, throwThe, MonadExceptOf.throw]
  | cons w ws =>
    constructor
    · intro h; exact ⟨w, ws, rfl, matchArgs_cons_inv h⟩
    · rintro ⟨w', ws', he, env1, h1, h2⟩
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [matchArgs.eq_2, h1]
      exact h2

theorem matchPat_bind_iff {st : σ} {ty : TypeId} {x : VarId} {sub : Pattern} {v : V}
    {env env' : Env V} :
    matchPat p sem st (.bind ty x sub) v env = .ok (some env') ↔
      x < env.size ∧ matchPat p sem st sub v (env.set! x (some v)) = .ok (some env') := by
  rw [matchPat.eq_1]
  split
  · simp [*]
  · simp [*, throw, throwThe, MonadExceptOf.throw]

theorem matchPat_wildcard_iff {st : σ} {ty : TypeId} {v : V} {env env' : Env V} :
    matchPat p sem st (.wildcard ty) v env = .ok (some env') ↔ env' = env := by
  rw [matchPat.eq_6]; simp [pure, Except.pure, eq_comm]

theorem matchPat_var_iff {st : σ} {ty : TypeId} {x : VarId} {v : V} {env env' : Env V} :
    matchPat p sem st (.var ty x) v env = .ok (some env') ↔
      ∃ w, env[x]? = some (some w) ∧ sem.eq v w = true ∧ env' = env := by
  rw [matchPat.eq_2]
  split
  · rename_i w hw
    simp only [pure, Except.pure, Except.ok.injEq]
    constructor
    · intro h
      split at h
      · exact ⟨w, hw, by assumption, (Option.some.inj h).symm⟩
      · cases h
    · rintro ⟨w', hw', he, rfl⟩
      rw [hw] at hw'
      cases hw'
      simp [he]
  · rename_i hne
    simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq, false_iff, not_exists, not_and]
    intro w hw
    exact absurd hw (hne w)

theorem matchPat_constBool_iff {st : σ} {ty : TypeId} {b : Bool} {v : V} {env env' : Env V} :
    matchPat p sem st (.constBool ty b) v env = .ok (some env') ↔
      sem.eq v (sem.bool b) = true ∧ env' = env := by
  rw [matchPat.eq_3]
  by_cases h : sem.eq v (sem.bool b) = true <;> simp [h, pure, Except.pure, eq_comm]

theorem matchPat_constInt_iff {st : σ} {ty : TypeId} {i : Int} {v : V} {env env' : Env V} :
    matchPat p sem st (.constInt ty i) v env = .ok (some env') ↔
      sem.eq v (sem.int ty i) = true ∧ env' = env := by
  rw [matchPat.eq_4]
  by_cases h : sem.eq v (sem.int ty i) = true <;> simp [h, pure, Except.pure, eq_comm]

theorem matchPat_constPrim_iff {st : σ} {ty : TypeId} {n : String} {v : V} {env env' : Env V} :
    matchPat p sem st (.constPrim ty n) v env = .ok (some env') ↔
      ∃ c, sem.prim ty n = some c ∧ sem.eq v c = true ∧ env' = env := by
  rw [matchPat.eq_5]
  cases hc : sem.prim ty n with
  | none => simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq, false_iff]; simp
  | some c =>
    simp only [Option.some.injEq, exists_eq_left']
    by_cases h : sem.eq v c = true
    · simp only [h, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Option.some.injEq, true_and]
      exact eq_comm
    · simp only [h, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq,
        reduceCtorEq, false_and]

/-- What a successful `.term` pattern match means, by the kind of the term. -/
def MatchTerm (p : Program) (sem : Sem V σ) (st : σ) (ty : TypeId) (t : TermId)
    (args : List Pattern) (v : V) (env env' : Env V) : Prop :=
  match termOf p t with
  | .error _ => False
  | .ok term =>
    match term.kind with
    | .enumVariant k => ∃ fs, sem.unData ty v = some (k, fs) ∧ matchArgs p sem st args fs env = .ok (some env')
    | .struct => ∃ k fs, sem.unData ty v = some (k, fs) ∧ matchArgs p sem st args fs env = .ok (some env')
    | .decl flags _ (some (.external _ _)) =>
      flags.isMulti = false ∧ ∃ fs, sem.extract term v st = .ok fs ∧
        matchArgs p sem st args fs env = .ok (some env')
    | _ => False

theorem matchPat_term_iff {st : σ} {ty : TypeId} {t : TermId} {args : List Pattern} {v : V}
    {env env' : Env V} :
    matchPat p sem st (.term ty t args) v env = .ok (some env') ↔
      MatchTerm p sem st ty t args v env env' := by
  rw [matchPat.eq_8]
  unfold MatchTerm
  cases termOf p t with
  | error e => simp [bind, Except.bind]
  | ok term =>
    simp only [M.except_ok_bind]
    cases hk : term.kind with
    | enumVariant k =>
      simp only
      cases hu : sem.unData ty v with
      | none => simp [throw, throwThe, MonadExceptOf.throw]
      | some q =>
        obtain ⟨k', fs⟩ := q
        simp only [Option.some.injEq, Prod.mk.injEq]
        by_cases hkk : k = k'
        · subst hkk
          simp
        · simp only [hkk, beq_iff_eq, ↓reduceIte, pure, Except.pure, Except.ok.injEq, reduceCtorEq,
            false_iff, not_exists, not_and]
          intro fs' h1; exact absurd h1.1.symm hkk
    | struct =>
      simp only
      cases hu : sem.unData ty v with
      | none => simp [throw, throwThe, MonadExceptOf.throw]
      | some q =>
        obtain ⟨k', fs⟩ := q
        constructor
        · intro h; exact ⟨k', fs, rfl, h⟩
        · rintro ⟨k'', fs', h1, h2⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          exact h2
    | decl flags c ex =>
      cases ex with
      | none => simp [throw, throwThe, MonadExceptOf.throw]
      | some ex =>
        cases ex with
        | internal f => simp [throw, throwThe, MonadExceptOf.throw]
        | external fn inf =>
          simp only
          cases hm : flags.isMulti with
          | true => simp [throw, throwThe, MonadExceptOf.throw]
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, true_and]
            cases he : sem.extract term v st with
            | ok fs => simp
            | fail =>
              cases inf <;> simp [throw, throwThe, MonadExceptOf.throw, pure, Except.pure]
            | unmodeled w => simp [throw, throwThe, MonadExceptOf.throw]

theorem matchIfLets_nil_iff {m : Nat} {env env' : Env V} {s s' : σ × Array RuleId} :
    (matchIfLets p sem cfg (m + 1) [] env).run s = .ok (some env', s') ↔ env' = env ∧ s' = s := by
  rw [matchIfLets.eq_2]; simp [eq_comm]

theorem matchIfLets_cons_iff {m : Nat} {il : IfLet} {ils : List IfLet} {env env' : Env V}
    {s s' : σ × Array RuleId} :
    (matchIfLets p sem cfg (m + 1) (il :: ils) env).run s = .ok (some env', s') ↔
      ∃ v s1, (evalExpr p sem cfg m il.rhs env).run s = .ok (some v, s1) ∧
        ∃ env1, matchPat p sem s1.1 il.lhs v env = .ok (some env1) ∧
          (matchIfLets p sem cfg m ils env1).run s1 = .ok (some env', s') := by
  rw [matchIfLets.eq_3]
  simp only [M.run_bind]
  constructor
  · intro h
    cases he : (evalExpr p sem cfg m il.rhs env).run s with
    | error e => rw [he] at h; cases h
    | ok q =>
      obtain ⟨o, s1⟩ := q
      rw [he] at h
      cases o with
      | none => simp at h
      | some v =>
        simp only [M.except_ok_bind, M.run_bind, M.run_get] at h
        cases hm : matchPat p sem s1.1 il.lhs v env with
        | error e => rw [hm] at h; cases h
        | ok o =>
          rw [hm] at h
          cases o with
          | none => simp at h
          | some env1 => exact ⟨v, s1, rfl, env1, hm, by simpa using h⟩
  · rintro ⟨v, s1, he, env1, hm, h⟩
    rw [he]
    simp only [M.except_ok_bind, M.run_bind, M.run_get, hm]
    simpa using h

/-! ## Evaluation -/

theorem evalExpr_var_iff {n : Nat} {ty : TypeId} {x : VarId} {env : Env V} {v : V}
    {s s' : σ × Array RuleId} :
    (evalExpr p sem cfg (n + 1) (.var ty x) env).run s = .ok (some v, s') ↔
      env[x]? = some (some v) ∧ s' = s := by
  rw [evalExpr.eq_2]
  split
  · rename_i w hw; simp [hw, eq_comm]
  · rename_i hne
    simp only [M.run_throw, reduceCtorEq, false_iff, not_and]
    intro h; exact absurd h (hne v)

theorem evalExpr_constBool_iff {n : Nat} {ty : TypeId} {b : Bool} {env : Env V} {v : V}
    {s s' : σ × Array RuleId} :
    (evalExpr p sem cfg (n + 1) (.constBool ty b) env).run s = .ok (some v, s') ↔
      v = sem.bool b ∧ s' = s := by
  rw [evalExpr.eq_3]; simp [eq_comm]

theorem evalExpr_constInt_iff {n : Nat} {ty : TypeId} {i : Int} {env : Env V} {v : V}
    {s s' : σ × Array RuleId} :
    (evalExpr p sem cfg (n + 1) (.constInt ty i) env).run s = .ok (some v, s') ↔
      v = sem.int ty i ∧ s' = s := by
  rw [evalExpr.eq_4]; simp [eq_comm]

theorem evalExpr_constPrim_iff {n : Nat} {ty : TypeId} {nm : String} {env : Env V} {v : V}
    {s s' : σ × Array RuleId} :
    (evalExpr p sem cfg (n + 1) (.constPrim ty nm) env).run s = .ok (some v, s') ↔
      sem.prim ty nm = some v ∧ s' = s := by
  rw [evalExpr.eq_5]
  cases h : sem.prim ty nm <;> simp [eq_comm]

theorem evalExpr_let_iff {n : Nat} {ty : TypeId} {bs : List (VarId × TypeId × Expr)} {body : Expr}
    {env : Env V} {v : V} {s s' : σ × Array RuleId} :
    (evalExpr p sem cfg (n + 1) (.let ty bs body) env).run s = .ok (some v, s') ↔
      ∃ env' s1, (evalBinds p sem cfg n bs env).run s = .ok (some env', s1) ∧
        (evalExpr p sem cfg n body env').run s1 = .ok (some v, s') := by
  rw [evalExpr.eq_6]
  simp only [M.run_bind]
  constructor
  · intro h
    cases he : (evalBinds p sem cfg n bs env).run s with
    | error e => rw [he] at h; cases h
    | ok q =>
      obtain ⟨o, s1⟩ := q
      rw [he] at h
      cases o with
      | none => simp at h
      | some env' => exact ⟨env', s1, rfl, h⟩
  · rintro ⟨env', s1, he, h⟩
    rw [he]; exact h

theorem evalExpr_term_iff {n : Nat} {ty : TypeId} {t : TermId} {args : List Expr}
    {env : Env V} {v : V} {s s' : σ × Array RuleId} :
    (evalExpr p sem cfg (n + 1) (.term ty t args) env).run s = .ok (some v, s') ↔
      ∃ vs s1, (evalArgs p sem cfg n args env).run s = .ok (some vs, s1) ∧
        (applyTerm p sem cfg n ty t vs).run s1 = .ok (some v, s') := by
  rw [evalExpr.eq_7]
  simp only [M.run_bind]
  constructor
  · intro h
    cases he : (evalArgs p sem cfg n args env).run s with
    | error e => rw [he] at h; cases h
    | ok q =>
      obtain ⟨o, s1⟩ := q
      rw [he] at h
      cases o with
      | none => simp at h
      | some vs => exact ⟨vs, s1, rfl, h⟩
  · rintro ⟨vs, s1, he, h⟩
    rw [he]; exact h

theorem evalArgs_nil_iff {n : Nat} {env : Env V} {vs : List V} {s s' : σ × Array RuleId} :
    (evalArgs p sem cfg (n + 1) [] env).run s = .ok (some vs, s') ↔ vs = [] ∧ s' = s := by
  rw [evalArgs.eq_2]; simp [eq_comm]

theorem evalArgs_cons_iff {n : Nat} {e : Expr} {es : List Expr} {env : Env V} {vs : List V}
    {s s' : σ × Array RuleId} :
    (evalArgs p sem cfg (n + 1) (e :: es) env).run s = .ok (some vs, s') ↔
      ∃ v s1 ws, (evalExpr p sem cfg n e env).run s = .ok (some v, s1) ∧
        (evalArgs p sem cfg n es env).run s1 = .ok (some ws, s') ∧ vs = v :: ws := by
  rw [evalArgs.eq_3]
  simp only [M.run_bind]
  constructor
  · intro h
    cases he : (evalExpr p sem cfg n e env).run s with
    | error e => rw [he] at h; cases h
    | ok q =>
      obtain ⟨o, s1⟩ := q
      rw [he] at h
      cases o with
      | none => simp at h
      | some v =>
        simp only [M.except_ok_bind, M.run_bind] at h
        cases ha : (evalArgs p sem cfg n es env).run s1 with
        | error e => rw [ha] at h; cases h
        | ok q' =>
          obtain ⟨o', s2⟩ := q'
          rw [ha] at h
          cases o' with
          | none => simp at h
          | some ws =>
            simp only [M.except_ok_bind, M.run_pure, Except.ok.injEq, Prod.mk.injEq,
              Option.some.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨v, s1, ws, rfl, ha, rfl⟩
  · rintro ⟨v, s1, ws, he, ha, rfl⟩
    rw [he]
    simp only [M.except_ok_bind, M.run_bind, ha]
    rfl

theorem evalBinds_nil_iff {n : Nat} {env env' : Env V} {s s' : σ × Array RuleId} :
    (evalBinds p sem cfg (n + 1) [] env).run s = .ok (some env', s') ↔ env' = env ∧ s' = s := by
  rw [evalBinds.eq_2]; simp [eq_comm]

theorem evalBinds_cons_iff {n : Nat} {x : VarId} {ty : TypeId} {e : Expr}
    {bs : List (VarId × TypeId × Expr)} {env env' : Env V} {s s' : σ × Array RuleId} :
    (evalBinds p sem cfg (n + 1) ((x, ty, e) :: bs) env).run s = .ok (some env', s') ↔
      ∃ v s1, (evalExpr p sem cfg n e env).run s = .ok (some v, s1) ∧ x < env.size ∧
        (evalBinds p sem cfg n bs (env.set! x (some v))).run s1 = .ok (some env', s') := by
  rw [evalBinds.eq_3]
  simp only [M.run_bind]
  constructor
  · intro h
    cases he : (evalExpr p sem cfg n e env).run s with
    | error e => rw [he] at h; cases h
    | ok q =>
      obtain ⟨o, s1⟩ := q
      rw [he] at h
      cases o with
      | none => simp at h
      | some v =>
        simp only [M.except_ok_bind] at h
        split at h
        · exact ⟨v, s1, rfl, by assumption, h⟩
        · cases h
  · rintro ⟨v, s1, he, hx, h⟩
    rw [he]
    simp only [M.except_ok_bind, hx, ↓reduceIte]
    exact h

/-- A successful call of an internal constructor, left for the callee's contract lemma. -/
def ApplyInternal (p : Program) (sem : Sem V σ) (cfg : Config) (n : Nat) (ty : TypeId)
    (t : TermId) (vs : List V) (s : σ × Array RuleId) (v : V) (s' : σ × Array RuleId) : Prop :=
  (applyTerm p sem cfg (n + 1) ty t vs).run s = .ok (some v, s')

/-- What a successful `applyTerm` means, by the kind of the term. -/
def ApplySpec (p : Program) (sem : Sem V σ) (cfg : Config) (n : Nat) (ty : TypeId) (t : TermId)
    (vs : List V) (s : σ × Array RuleId) (v : V) (s' : σ × Array RuleId) : Prop :=
  match termOf p t with
  | .error _ => False
  | .ok term =>
    match term.kind with
    | .enumVariant k => v = sem.mkData ty k vs ∧ s' = s
    | .struct => v = sem.mkData ty 0 vs ∧ s' = s
    | .decl flags (some (.external _)) _ =>
      flags.isMulti = false ∧ ∃ st', sem.ctor term vs s.1 = .ok (v, st') ∧ s' = (st', s.2)
    | .decl flags (some .internal) _ =>
      flags.isMulti = false ∧ ApplyInternal p sem cfg n ty t vs s v s'
    | _ => False

theorem applyTerm_iff {n : Nat} {ty : TypeId} {t : TermId} {vs : List V} {v : V}
    {s s' : σ × Array RuleId} :
    (applyTerm p sem cfg (n + 1) ty t vs).run s = .ok (some v, s') ↔
      ApplySpec p sem cfg n ty t vs s v s' := by
  unfold ApplySpec ApplyInternal
  cases ht : termOf p t with
  | error e =>
    rw [applyTerm.eq_2, ht]
    simp [liftM, monadLift, MonadLift.monadLift, StateT.lift, bind, StateT.bind, Except.bind,
      StateT.run]
  | ok term =>
    simp only
    have e0 : (applyTerm p sem cfg (n + 1) ty t vs).run s =
        (match term.kind with
        | .enumVariant k => pure (some (sem.mkData ty k vs))
        | .struct => pure (some (sem.mkData ty 0 vs))
        | .decl flags (some (.external _)) _ =>
          if flags.isMulti then throw (.unsupported s!"multi constructor {term.name}") else do
          let (st, tr) ← get
          match sem.ctor term vs st with
          | .ok (v, st') => do set (st', tr); pure (some v)
          | .fail => if flags.isPartial then pure none else throw (.infallibleFailed term.name)
          | .unmodeled w => throw (.unmodeled w)
        | .decl flags (some .internal) _ =>
          if flags.isMulti then throw (.unsupported s!"multi constructor {term.name}") else do
          match ← selectRule p sem cfg n term (p.rulesOf t) vs with
          | none => if flags.isPartial then pure none else throw (.noRule term.name)
          | some (r, env) => do
            match ← evalExpr p sem cfg n r.rhs env with
            | some v => do fire r.id; pure (some v)
            | none => pure none
        | _ => throw (.malformed s!"term {term.name} has no constructor") : M σ (Option V)).run s := by
      rw [applyTerm.eq_2, ht]; rfl
    cases hk : term.kind with
    | enumVariant k => rw [e0, hk]; simp [eq_comm]
    | struct => rw [e0, hk]; simp [eq_comm]
    | decl flags c ex =>
      cases c with
      | none => rw [e0, hk]; simp
      | some c =>
        cases c with
        | internal =>
          simp only
          constructor
          · intro h
            refine ⟨?_, h⟩
            rw [e0, hk] at h
            cases hm : flags.isMulti
            · rfl
            · simp [hm] at h
          · rintro ⟨-, h⟩; exact h
        | external fn =>
          rw [e0, hk]
          simp only
          cases hm : flags.isMulti
          · simp only [Bool.false_eq_true, ↓reduceIte, true_and, M.run_bind, M.run_get,
              M.except_ok_bind]
            cases hc : sem.ctor term vs s.1 with
            | ok q =>
              obtain ⟨v', st'⟩ := q
              simp only [hc, Functor.map, Except.map, M.run_bind, M.run_set, M.except_ok_bind,
                M.run_pure, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq, ExtResult.ok.injEq]
              constructor
              · rintro ⟨rfl, rfl⟩; exact ⟨st', ⟨rfl, rfl⟩, rfl⟩
              · rintro ⟨st'', ⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩
            | fail =>
              simp only [hc]
              cases hp : flags.isPartial <;> simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
            | unmodeled w => simp
          · simp

end Isle.Interp
