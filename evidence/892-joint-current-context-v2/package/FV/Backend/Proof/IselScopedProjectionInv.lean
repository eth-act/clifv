import FV.Backend.Proof.IselScopedProjection

/-!
State projection for a constructor-closed part of an ISLE program, under a state invariant.

`evaluation_scoped_restate` needs every allowed constructor to agree with the base embedding in
every state, and every rule of an allowed internal term to stay in scope. A lowering driver can
revise a constructor so that it agrees only on the states it actually reaches (for example, the
Stock driver's `put_in_reg` refuses a value whose defining instruction it has sunk), and a term
can have rules outside the scope whose argument patterns never match the values at hand. Here
constructors agree on states that satisfy `inv` and preserve it, and a rule outside the scope is
admitted when its argument patterns cannot match the given values. The program stays abstract.
-/

namespace Isle.Interp

/-- From a state that satisfies `inv`, both runs agree after projection, and every successful run
of the restated computation ends in a state that satisfies `inv`. -/
def ProjectsInv {σ τ α : Type} (project : τ → σ) (inv : τ → Prop) (x : M τ α) (y : M σ α) : Prop :=
  ∀ st tr, inv st →
    projectResult project (x.run (st, tr)) = y.run (project st, tr) ∧
    ∀ a next trace, x.run (st, tr) = .ok (a, next, trace) → inv next

/-- A rule whose argument patterns cannot match the values `vs` in any embedding state. -/
def ArgsFail {V σ : Type} (p : Program) (sem : Sem V σ) (r : Rule) (vs : List V) : Prop :=
  ∀ st env, matchArgs p sem st r.args vs (Array.replicate r.vars.length none) ≠ .ok (some env)

/-- Allowed constructors agree with the base embedding on states that satisfy `inv` and preserve
it; every rule of an allowed internal term is in scope or cannot match its arguments. -/
structure ProjectionScopeInv {V σ τ : Type} (p : Program) (sem : Sem V σ)
    (project : τ → σ) (inv : τ → Prop) (ctor : Term → List V → τ → ExtResult (V × τ))
    (allowed : TermId → Prop) : Prop where
  agree : ∀ t term, allowed t → termOf p t = .ok term →
    ∀ vs st, inv st → projectCtor project (ctor term vs st) = sem.ctor term vs (project st)
  preserve : ∀ t term, allowed t → termOf p t = .ok term →
    ∀ vs st v st', inv st → ctor term vs st = .ok (v, st') → inv st'
  rules : ∀ t term, allowed t → termOf p t = .ok term →
    ∀ flags ex, term.kind = .decl flags (some .internal) ex →
      ∀ vs, ∀ r ∈ p.rulesOf t, RuleScoped allowed r ∨ ArgsFail p sem r vs

private theorem inv_pure {σ τ α : Type} (project : τ → σ) (inv : τ → Prop) (a : α) :
    ProjectsInv project inv (pure a) (pure a) := by
  intro st tr hst
  refine ⟨rfl, ?_⟩
  intro a' next trace h
  simp only [StateT.run, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  rw [← h.2.1]
  exact hst

private theorem inv_throw {σ τ α : Type} (project : τ → σ) (inv : τ → Prop) (err : Err) :
    ProjectsInv project inv (throw err : M τ α) (throw err) := by
  intro st tr _
  refine ⟨rfl, ?_⟩
  intro a next trace h
  cases h

private theorem inv_lift {σ τ α : Type} (project : τ → σ) (inv : τ → Prop) (x : Except Err α) :
    ProjectsInv project inv (liftM x) (liftM x) := by
  intro st tr hst
  cases x with
  | error e => exact ⟨rfl, fun a next trace h => by cases h⟩
  | ok a =>
    refine ⟨rfl, ?_⟩
    intro a' next trace h
    simp only [M.run_liftM_ok, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2.1]
    exact hst

private theorem inv_bind {σ τ α β : Type} (project : τ → σ) (inv : τ → Prop)
    {x : M τ α} {y : M σ α} {f : α → M τ β} {g : α → M σ β}
    (hx : ProjectsInv project inv x y)
    (hf : ∀ st tr a next trace, inv st → x.run (st, tr) = .ok (a, next, trace) →
      ProjectsInv project inv (f a) (g a)) :
    ProjectsInv project inv (x >>= f) (y >>= g) := by
  intro st tr hst
  obtain ⟨hagree, hpres⟩ := hx st tr hst
  change projectResult project (x.run (st, tr) >>= fun a => (f a.1).run a.2) =
      (y.run (project st, tr) >>= fun a => (g a.1).run a.2) ∧
    ∀ b next trace, (x.run (st, tr) >>= fun a => (f a.1).run a.2) = .ok (b, next, trace) → inv next
  cases he : x.run (st, tr) with
  | error e =>
    simp only [he, projectResult] at hagree
    refine ⟨by rw [← hagree]; rfl, fun b next trace h => by cases h⟩
  | ok a =>
    rcases a with ⟨a, next, trace⟩
    simp only [he, projectResult] at hagree
    have hnext := hpres a next trace he
    obtain ⟨hagree', hpres'⟩ := hf st tr a next trace hst he next trace hnext
    refine ⟨by rw [← hagree]; exact hagree', ?_⟩
    intro b next' trace' h
    exact hpres' b next' trace' h

private theorem inv_bind_all {σ τ α β : Type} (project : τ → σ) (inv : τ → Prop)
    {x : M τ α} {y : M σ α} {f : α → M τ β} {g : α → M σ β}
    (hx : ProjectsInv project inv x y) (hf : ∀ a, ProjectsInv project inv (f a) (g a)) :
    ProjectsInv project inv (x >>= f) (y >>= g) :=
  inv_bind project inv hx (fun _ _ a _ _ _ _ => hf a)

private theorem inv_get {σ τ α : Type} (project : τ → σ) (inv : τ → Prop)
    {f : (τ × Array RuleId) → M τ α} {g : (σ × Array RuleId) → M σ α}
    (hf : ∀ st tr, inv st → ProjectsInv project inv (f (st, tr)) (g (project st, tr))) :
    ProjectsInv project inv (get >>= f) (get >>= g) := by
  intro st tr hst
  exact hf st tr hst st tr hst

private theorem inv_set {σ τ : Type} (project : τ → σ) (inv : τ → Prop) (st : τ) (hst : inv st)
    (tr : Array RuleId) : ProjectsInv project inv (set (st, tr)) (set (project st, tr)) := by
  intro initial trace _
  refine ⟨rfl, ?_⟩
  intro a next trace' h
  simp only [StateT.run, set, StateT.set, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  rw [← h.2.1]
  exact hst

private theorem inv_fire {σ τ : Type} (project : τ → σ) (inv : τ → Prop) (r : RuleId) :
    ProjectsInv project inv (fire r) (fire r) := by
  intro st tr hst
  refine ⟨rfl, ?_⟩
  intro a next trace h
  have hrun : (fire r : M τ Unit).run (st, tr) = .ok ((), st, tr.push r) := rfl
  rw [hrun] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  rw [← h.2.1]
  exact hst

structure EvaluationScopedProjectsInv {V σ τ : Type} (p : Program) (sem : Sem V σ)
    (cfg : Config) (project : τ → σ) (inv : τ → Prop)
    (ctor : Term → List V → τ → ExtResult (V × τ))
    (extract : Term → V → τ → ExtResult (List V)) (allowed : TermId → Prop) (n : Nat) : Prop where
  expr : ∀ e env, ExprScoped allowed e →
    ProjectsInv project inv (evalExpr p (sem.restate ctor extract) cfg n e env) (evalExpr p sem cfg n e env)
  args : ∀ es env, ArgsScoped allowed es →
    ProjectsInv project inv (evalArgs p (sem.restate ctor extract) cfg n es env) (evalArgs p sem cfg n es env)
  binds : ∀ bs env, BindsScoped allowed bs →
    ProjectsInv project inv (evalBinds p (sem.restate ctor extract) cfg n bs env)
      (evalBinds p sem cfg n bs env)
  term : ∀ ty t vs, allowed t →
    ProjectsInv project inv (applyTerm p (sem.restate ctor extract) cfg n ty t vs)
      (applyTerm p sem cfg n ty t vs)
  rule : ∀ r vs, IfLetsScoped allowed r.iflets ∨ ArgsFail p sem r vs →
    ProjectsInv project inv (matchRule p (sem.restate ctor extract) cfg n r vs) (matchRule p sem cfg n r vs)
  iflets : ∀ ils env, IfLetsScoped allowed ils →
    ProjectsInv project inv (matchIfLets p (sem.restate ctor extract) cfg n ils env)
      (matchIfLets p sem cfg n ils env)
  tryRule : ∀ r vs, IfLetsScoped allowed r.iflets ∨ ArgsFail p sem r vs →
    ProjectsInv project inv (Interp.tryRule p (sem.restate ctor extract) cfg n r vs)
      (Interp.tryRule p sem cfg n r vs)
  select : ∀ t rs vs, (∀ r ∈ rs, IfLetsScoped allowed r.iflets ∨ ArgsFail p sem r vs) →
    ProjectsInv project inv (selectRule p (sem.restate ctor extract) cfg n t rs vs)
      (selectRule p sem cfg n t rs vs)

/-- A selected rule matched its arguments, so it is not one that cannot match them. -/
private theorem selected_scoped {V σ τ : Type} {p : Program} {sem : Sem V σ} {cfg : Config}
    (hc : cfg.checkOverlap = false) {project : τ → σ} {ctor : Term → List V → τ → ExtResult (V × τ)}
    {extract : Term → V → τ → ExtResult (List V)} {allowed : TermId → Prop}
    (hextract : ∀ t v st, extract t v st = sem.extract t v (project st)) {n : Nat} {term : Term}
    {rs : List Rule} {vs : List V} {s s' : τ × Array RuleId} {r : Rule} {env : Env V}
    (hrules : ∀ r ∈ rs, RuleScoped allowed r ∨ ArgsFail p sem r vs)
    (hselect : (selectRule p (sem.restate ctor extract) cfg n term rs vs).run s = .ok (some (r, env), s')) :
    r ∈ rs ∧ RuleScoped allowed r := by
  obtain ⟨hr, m, -, hm⟩ := selectRule_some hc hselect
  refine ⟨hr, ?_⟩
  rcases hrules r hr with h | hfail
  · exact h
  · exfalso
    cases m with
    | zero => rw [matchRule.eq_1] at hm; cases hm
    | succ m =>
      obtain ⟨env0, hargs, -⟩ := matchRule_some_inv hm
      rw [matchArgs_restate p sem project ctor extract hextract] at hargs
      exact hfail _ _ hargs

/-- Project every interpreter phase in a closed helper scope from states that satisfy the
invariant, with the compiler's first-match configuration; values, errors and traces agree, and
the invariant holds after every successful run. -/
theorem evaluation_scoped_restate_inv {V σ τ : Type} (p : Program) (sem : Sem V σ)
    (cfg : Config) (hc : cfg.checkOverlap = false) (project : τ → σ) (inv : τ → Prop)
    (ctor : Term → List V → τ → ExtResult (V × τ))
    (extract : Term → V → τ → ExtResult (List V)) (allowed : TermId → Prop)
    (hscope : ProjectionScopeInv p sem project inv ctor allowed)
    (hextract : ∀ t v st, extract t v st = sem.extract t v (project st)) (n : Nat) :
    EvaluationScopedProjectsInv p sem cfg project inv ctor extract allowed n := by
  induction n with
  | zero => constructor <;> intros <;> exact inv_throw project inv .outOfFuel
  | succ n ih =>
    constructor
    · intro e env hs
      cases e with
      | var ty x =>
        rw [evalExpr.eq_2, evalExpr.eq_2]
        split <;> first | exact inv_pure project inv _ | exact inv_throw project inv _
      | constBool ty b => exact inv_pure project inv _
      | constInt ty i => exact inv_pure project inv _
      | constPrim ty name =>
        rw [evalExpr.eq_5, evalExpr.eq_5]
        dsimp only [Sem.restate]
        split <;> first | exact inv_pure project inv _ | exact inv_throw project inv _
      | «let» ty bs body =>
        rw [evalExpr.eq_6, evalExpr.eq_6]
        apply inv_bind_all project inv (ih.binds bs env (fun t ht => hs t (List.mem_append_left _ ht)))
        intro result
        cases result with
        | none => exact inv_pure project inv _
        | some env' => exact ih.expr body env' (fun t ht => hs t (List.mem_append_right _ ht))
      | term ty t es =>
        rw [evalExpr.eq_7, evalExpr.eq_7]
        apply inv_bind_all project inv (ih.args es env (fun u hu => hs u (List.mem_cons_of_mem _ hu)))
        intro result
        cases result with
        | none => exact inv_pure project inv _
        | some vs => exact ih.term ty t vs (hs t (List.mem_cons_self ..))
    · intro es env hs
      cases es with
      | nil => exact inv_pure project inv _
      | cons e es =>
        rw [evalArgs.eq_3, evalArgs.eq_3]
        apply inv_bind_all project inv (ih.expr e env (fun t ht => hs t (List.mem_append_left _ ht)))
        intro result
        cases result with
        | none => exact inv_pure project inv _
        | some v =>
          dsimp only
          apply inv_bind_all project inv (ih.args es env (fun t ht => hs t (List.mem_append_right _ ht)))
          intro result
          cases result <;> exact inv_pure project inv _
    · intro bs env hs
      cases bs with
      | nil => exact inv_pure project inv _
      | cons b bs =>
        rcases b with ⟨x, ty, e⟩
        rw [evalBinds.eq_3, evalBinds.eq_3]
        apply inv_bind_all project inv (ih.expr e env (fun t ht => hs t (List.mem_append_left _ ht)))
        intro result
        cases result with
        | none => exact inv_pure project inv _
        | some v =>
          dsimp only
          split
          · exact ih.binds bs (env.set! x (some v)) (fun t ht => hs t (List.mem_append_right _ ht))
          · exact inv_throw project inv _
    · intro ty t vs hs
      rw [applyTerm.eq_2, applyTerm.eq_2]
      apply inv_bind project inv (inv_lift project inv (termOf p t))
      intro initial trace term next tr _ hterm
      have ht : termOf p t = .ok term := by
        cases he : termOf p t with
        | error e => rw [he] at hterm; cases hterm
        | ok actual =>
          rw [he] at hterm
          simp only [M.run_liftM_ok, Except.ok.injEq, Prod.mk.injEq] at hterm
          exact congrArg Except.ok hterm.1
      cases hk : term.kind <;> try dsimp only
      · exact inv_pure project inv _
      · exact inv_pure project inv _
      · rename_i flags c ex
        cases c with
        | none => exact inv_throw project inv _
        | some c =>
          cases c with
          | external name =>
            dsimp only
            split
            · exact inv_throw project inv _
            · apply inv_get project inv
              intro st tr hst
              dsimp only [Sem.restate]
              have hc' := hscope.agree t term hs ht vs st hst
              have hp := hscope.preserve t term hs ht vs st
              cases he : ctor term vs st with
              | ok a =>
                rcases a with ⟨v, next⟩
                simp only [he, projectCtor] at hc'
                rw [← hc']
                dsimp only
                exact inv_bind_all project inv (inv_set project inv next (hp v next hst he) tr)
                  (fun _ => inv_pure project inv _)
              | fail =>
                simp only [he, projectCtor] at hc'
                rw [← hc']
                dsimp only
                split <;> first | exact inv_pure project inv _ | exact inv_throw project inv _
              | unmodeled w =>
                simp only [he, projectCtor] at hc'
                rw [← hc']
                exact inv_throw project inv _
          | internal =>
            dsimp only
            split
            · exact inv_throw project inv _
            · have hrules := hscope.rules t term hs ht flags ex hk vs
              apply inv_bind project inv
                (ih.select term (p.rulesOf t) vs (fun r hr => (hrules r hr).imp_left And.left))
              intro start trace result next tr _ hselect
              cases result with
              | none =>
                dsimp only
                split <;> first | exact inv_pure project inv _ | exact inv_throw project inv _
              | some pair =>
                rcases pair with ⟨r, env⟩
                have he := (selected_scoped hc hextract hrules hselect).2.2
                dsimp only
                apply inv_bind_all project inv (ih.expr r.rhs env he)
                intro result
                cases result with
                | none => exact inv_pure project inv _
                | some v =>
                  exact inv_bind_all project inv (inv_fire project inv r.id)
                    (fun _ => inv_pure project inv _)
    · intro r vs hs
      rw [matchRule.eq_2, matchRule.eq_2]
      apply inv_get project inv
      intro st tr hst
      dsimp only
      rw [matchArgs_restate p sem project ctor extract hextract]
      apply inv_bind project inv (inv_lift project inv _)
      intro _ _ result _ _ _ hargs
      cases result with
      | none => exact inv_pure project inv _
      | some env =>
        rcases hs with hs | hfail
        · exact ih.iflets r.iflets env hs
        · exfalso
          cases hm : matchArgs p sem (project st) r.args vs (Array.replicate r.vars.length none) with
          | error e => rw [hm] at hargs; cases hargs
          | ok res =>
            rw [hm] at hargs
            simp only [M.run_liftM_ok, Except.ok.injEq, Prod.mk.injEq] at hargs
            rw [hargs.1] at hm
            exact hfail _ _ hm
    · intro ils env hs
      cases ils with
      | nil => exact inv_pure project inv _
      | cons il ils =>
        rw [matchIfLets.eq_3, matchIfLets.eq_3]
        apply inv_bind_all project inv (ih.expr il.rhs env (hs il (List.mem_cons_self ..)))
        intro result
        cases result with
        | none => exact inv_pure project inv _
        | some v =>
          dsimp only
          apply inv_get project inv
          intro st tr _
          dsimp only
          rw [matchPat_restate p sem project ctor extract hextract]
          apply inv_bind_all project inv (inv_lift project inv _)
          intro result
          cases result with
          | none => exact inv_pure project inv _
          | some env' => exact ih.iflets ils env' (fun q hq => hs q (List.mem_cons_of_mem _ hq))
    · intro r vs hs
      rw [tryRule.eq_2, tryRule.eq_2]
      apply inv_get project inv
      intro st tr hst
      apply inv_bind_all project inv (ih.rule r vs hs)
      intro result
      cases result with
      | some env => exact inv_pure project inv _
      | none =>
        dsimp only
        exact inv_bind_all project inv (inv_set project inv st hst tr) (fun _ => inv_pure project inv _)
    · intro term rs vs hs
      cases rs with
      | nil => exact inv_pure project inv _
      | cons r rs =>
        rw [selectRule.eq_3, selectRule.eq_3]
        apply inv_bind_all project inv (ih.tryRule r vs (hs r (List.mem_cons_self ..)))
        intro result
        cases result with
        | none => exact ih.select term rs vs (fun q hq => hs q (List.mem_cons_of_mem _ hq))
        | some env => simp only [hc, Bool.false_eq_true, ite_false]; exact inv_pure project inv _

/-- A run of one internal term outside the allowed scope agrees on arguments for which each of
its rules is in scope or cannot match (for example a lowering entry term whose remaining rules
need instruction shapes the arguments do not have). -/
theorem applyTerm_internal_restate_inv {V σ τ : Type} (p : Program) (sem : Sem V σ)
    (cfg : Config) (hc : cfg.checkOverlap = false) (project : τ → σ) (inv : τ → Prop)
    (ctor : Term → List V → τ → ExtResult (V × τ))
    (extract : Term → V → τ → ExtResult (List V)) (allowed : TermId → Prop)
    (hscope : ProjectionScopeInv p sem project inv ctor allowed)
    (hextract : ∀ t v st, extract t v st = sem.extract t v (project st)) (n : Nat)
    {ty : TypeId} {t : TermId} {vs : List V} {term : Term} {flags : TermFlags} {ex : Option Extractor}
    (ht : termOf p t = .ok term) (hk : term.kind = .decl flags (some .internal) ex)
    (hrules : ∀ r ∈ p.rulesOf t, RuleScoped allowed r ∨ ArgsFail p sem r vs) :
    ProjectsInv project inv (applyTerm p (sem.restate ctor extract) cfg (n + 1) ty t vs)
      (applyTerm p sem cfg (n + 1) ty t vs) := by
  have ih := evaluation_scoped_restate_inv p sem cfg hc project inv ctor extract allowed hscope hextract n
  rw [applyTerm.eq_2, applyTerm.eq_2]
  apply inv_bind project inv (inv_lift project inv (termOf p t))
  intro initial trace term' next tr _ hterm
  rw [ht] at hterm
  simp only [M.run_liftM_ok, Except.ok.injEq, Prod.mk.injEq] at hterm
  obtain ⟨rfl, -, -⟩ := hterm
  rw [hk]
  dsimp only
  split
  · exact inv_throw project inv _
  · apply inv_bind project inv
      (ih.select term (p.rulesOf t) vs (fun r hr => (hrules r hr).imp_left And.left))
    intro start trace' result next' tr' _ hselect
    cases result with
    | none =>
      dsimp only
      split <;> first | exact inv_pure project inv _ | exact inv_throw project inv _
    | some pair =>
      rcases pair with ⟨r, env⟩
      have he := (selected_scoped hc hextract hrules hselect).2.2
      dsimp only
      apply inv_bind_all project inv (ih.expr r.rhs env he)
      intro result
      cases result with
      | none => exact inv_pure project inv _
      | some v =>
        exact inv_bind_all project inv (inv_fire project inv r.id) (fun _ => inv_pure project inv _)

/-- Rule selection agrees on arguments for which every candidate rule has `if-let`s in scope or
cannot match them; the selected rule's right-hand side may be out of scope. -/
theorem selectRule_restate_inv {V σ τ : Type} (p : Program) (sem : Sem V σ)
    (cfg : Config) (hc : cfg.checkOverlap = false) (project : τ → σ) (inv : τ → Prop)
    (ctor : Term → List V → τ → ExtResult (V × τ))
    (extract : Term → V → τ → ExtResult (List V)) (allowed : TermId → Prop)
    (hscope : ProjectionScopeInv p sem project inv ctor allowed)
    (hextract : ∀ t v st, extract t v st = sem.extract t v (project st)) (n : Nat) (term : Term)
    {rs : List Rule} {vs : List V}
    (hrules : ∀ r ∈ rs, IfLetsScoped allowed r.iflets ∨ ArgsFail p sem r vs) :
    ProjectsInv project inv (selectRule p (sem.restate ctor extract) cfg n term rs vs)
      (selectRule p sem cfg n term rs vs) :=
  (evaluation_scoped_restate_inv p sem cfg hc project inv ctor extract allowed hscope hextract
    n).select term rs vs hrules

/-- Every unconditional scope is a guarded scope with the trivial invariant. -/
theorem ProjectionScope.toInv {V σ τ : Type} {p : Program} {sem : Sem V σ} {project : τ → σ}
    {ctor : Term → List V → τ → ExtResult (V × τ)} {allowed : TermId → Prop}
    (h : ProjectionScope p sem project ctor allowed) :
    ProjectionScopeInv p sem project (fun _ => True) ctor allowed :=
  ⟨fun t term ha ht vs st _ => h.ctor t term ha ht vs st, fun _ _ _ _ _ _ _ _ _ _ => trivial,
    fun t term ha ht flags ex hk _ r hr => .inl (h.rules t term ha ht flags ex hk r hr)⟩

/-! Concrete witness: the rollback example of `evaluation_scoped_restate_witness`, through the
guarded projection with the trivial invariant. -/

private theorem witness_scope : ProjectionScope ProjectionWitness.program ProjectionWitness.sem
    Prod.fst ProjectionWitness.ctor (fun t => t = 0 ∨ t = 1) := by
  constructor
  · intro t term hs ht vs st
    rfl
  · intro t term hs ht flags ex hk r hr
    rcases hs with rfl | rfl
    · change r ∈ [ProjectionWitness.failed, ProjectionWitness.accepted] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls, ProjectionWitness.failed]
      · constructor
        · change ∀ il ∈ ([] : List IfLet), ExprScoped _ il.rhs
          simp
        · simp [ExprScoped, exprCalls, argCalls, ProjectionWitness.accepted]
    · change r ∈ ([] : List Rule) at hr
      cases hr

theorem evaluation_scoped_restate_inv_witness :
    projectResult Prod.fst
      ((applyTerm ProjectionWitness.program
        (ProjectionWitness.sem.restate ProjectionWitness.ctor ProjectionWitness.extract)
        {} 100 0 0 [7]).run ((10, 0), #[])) =
      (applyTerm ProjectionWitness.program ProjectionWitness.sem {} 100 0 0 [7]).run (10, #[]) ∧
    (applyTerm ProjectionWitness.program
      (ProjectionWitness.sem.restate ProjectionWitness.ctor ProjectionWitness.extract)
      {} 100 0 0 [7]).run ((10, 0), #[]) = .ok (some 7, (11, 1), #[1]) :=
  ⟨((evaluation_scoped_restate_inv _ _ {} rfl Prod.fst (fun _ => True) _ _ _
    (ProjectionScope.toInv witness_scope) (fun _ _ _ => rfl) 100).term 0 0 [7] (Or.inl rfl)
    (10, 0) #[] trivial).1, rfl⟩

end Isle.Interp
