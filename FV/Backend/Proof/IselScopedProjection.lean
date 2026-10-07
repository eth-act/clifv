import FV.Isle.InterpProjection
import FV.Backend.Proof.IselGeneric

/-!
State projection for a constructor-closed part of an ISLE program. The program
itself stays abstract; closure facts concern individual exported rules and terms.
This permits reuse of helpers such as constant materialization when unrelated
constructors elsewhere in the program intentionally change semantics.
-/

namespace Isle.Interp

mutual
def exprCalls : Expr → List TermId
  | .var .. | .constBool .. | .constInt .. | .constPrim .. => []
  | .let _ bs body => bindCalls bs ++ exprCalls body
  | .term _ t es => t :: argCalls es
def argCalls : List Expr → List TermId
  | [] => []
  | e :: es => exprCalls e ++ argCalls es
def bindCalls : List (VarId × TypeId × Expr) → List TermId
  | [] => []
  | (_, _, e) :: bs => exprCalls e ++ bindCalls bs
end

def ExprScoped (allowed : TermId → Prop) (e : Expr) : Prop :=
  ∀ t ∈ exprCalls e, allowed t

def ArgsScoped (allowed : TermId → Prop) (es : List Expr) : Prop :=
  ∀ t ∈ argCalls es, allowed t

def BindsScoped (allowed : TermId → Prop) (bs : List (VarId × TypeId × Expr)) : Prop :=
  ∀ t ∈ bindCalls bs, allowed t

def IfLetsScoped (allowed : TermId → Prop) (ils : List IfLet) : Prop :=
  ∀ il ∈ ils, ExprScoped allowed il.rhs

def RuleScoped (allowed : TermId → Prop) (r : Rule) : Prop :=
  IfLetsScoped allowed r.iflets ∧ ExprScoped allowed r.rhs

/-- Closure and constructor agreement only for terms reachable from the helper.
Extractors remain globally equal because patterns only read embedding state. -/
structure ProjectionScope {V σ τ : Type} (p : Program) (sem : Sem V σ)
    (project : τ → σ) (ctor : Term → List V → τ → ExtResult (V × τ))
    (allowed : TermId → Prop) : Prop where
  ctor : ∀ t term, allowed t → termOf p t = .ok term →
    ∀ vs st, projectCtor project (ctor term vs st) = sem.ctor term vs (project st)
  rules : ∀ t term, allowed t → termOf p t = .ok term →
    ∀ flags ex, term.kind = .decl flags (some .internal) ex →
      ∀ r ∈ p.rulesOf t, RuleScoped allowed r

private theorem scoped_pure {σ τ α : Type} (project : τ → σ) (a : α) :
    Projects project (pure a) (pure a) := by intro st tr; rfl

private theorem scoped_throw {σ τ α : Type} (project : τ → σ) (err : Err) :
    Projects project (throw err : M τ α) (throw err) := by intro st tr; rfl

private theorem scoped_lift {σ τ α : Type} (project : τ → σ) (x : Except Err α) :
    Projects project (liftM x) (liftM x) := by intro st tr; cases x <;> rfl

private theorem scoped_bind {σ τ α β : Type} (project : τ → σ)
    {x : M τ α} {y : M σ α} {f : α → M τ β} {g : α → M σ β}
    (hx : Projects project x y)
    (hf : ∀ st tr a next trace, x.run (st, tr) = .ok (a, next, trace) →
      projectResult project ((f a).run (next, trace)) = (g a).run (project next, trace)) :
    Projects project (x >>= f) (y >>= g) := by
  intro st tr
  have h := hx st tr
  change projectResult project (x.run (st, tr) >>= fun a => (f a.1).run a.2) =
    (y.run (project st, tr) >>= fun a => (g a.1).run a.2)
  cases he : x.run (st, tr) with
  | error e => simp only [he, projectResult] at h; rw [← h]; rfl
  | ok a =>
    rcases a with ⟨a, next, trace⟩
    simp only [he, projectResult] at h
    rw [← h]
    exact hf st tr a next trace he

private theorem scoped_bind_all {σ τ α β : Type} (project : τ → σ)
    {x : M τ α} {y : M σ α} {f : α → M τ β} {g : α → M σ β}
    (hx : Projects project x y) (hf : ∀ a, Projects project (f a) (g a)) :
    Projects project (x >>= f) (y >>= g) :=
  scoped_bind project hx (fun _ _ a next trace _ => hf a next trace)

private theorem scoped_get {σ τ α : Type} (project : τ → σ)
    {f : (τ × Array RuleId) → M τ α} {g : (σ × Array RuleId) → M σ α}
    (hf : ∀ st tr, Projects project (f (st, tr)) (g (project st, tr))) :
    Projects project (get >>= f) (get >>= g) := by intro st tr; exact hf st tr st tr

private theorem scoped_set {σ τ : Type} (project : τ → σ) (st : τ)
    (tr : Array RuleId) : Projects project (set (st, tr)) (set (project st, tr)) := by
  intro initial trace; rfl

private theorem scoped_fire {σ τ : Type} (project : τ → σ) (r : RuleId) :
    Projects project (fire r) (fire r) := by intro st tr; rfl

structure EvaluationScopedProjects {V σ τ : Type} (p : Program) (sem : Sem V σ)
    (cfg : Config) (project : τ → σ)
    (ctor : Term → List V → τ → ExtResult (V × τ))
    (extract : Term → V → τ → ExtResult (List V)) (allowed : TermId → Prop) (n : Nat) : Prop where
  expr : ∀ e env, ExprScoped allowed e →
    Projects project (evalExpr p (sem.restate ctor extract) cfg n e env) (evalExpr p sem cfg n e env)
  args : ∀ es env, ArgsScoped allowed es →
    Projects project (evalArgs p (sem.restate ctor extract) cfg n es env) (evalArgs p sem cfg n es env)
  binds : ∀ bs env, BindsScoped allowed bs →
    Projects project (evalBinds p (sem.restate ctor extract) cfg n bs env) (evalBinds p sem cfg n bs env)
  term : ∀ ty t vs, allowed t →
    Projects project (applyTerm p (sem.restate ctor extract) cfg n ty t vs) (applyTerm p sem cfg n ty t vs)
  rule : ∀ r vs, RuleScoped allowed r →
    Projects project (matchRule p (sem.restate ctor extract) cfg n r vs) (matchRule p sem cfg n r vs)
  iflets : ∀ ils env, IfLetsScoped allowed ils →
    Projects project (matchIfLets p (sem.restate ctor extract) cfg n ils env) (matchIfLets p sem cfg n ils env)
  tryRule : ∀ r vs, RuleScoped allowed r →
    Projects project (Interp.tryRule p (sem.restate ctor extract) cfg n r vs) (Interp.tryRule p sem cfg n r vs)
  select : ∀ t rs vs, (∀ r ∈ rs, RuleScoped allowed r) →
    Projects project (selectRule p (sem.restate ctor extract) cfg n t rs vs) (selectRule p sem cfg n t rs vs)

/-- Project every interpreter phase in a closed helper scope. The compiler's
ordinary first-match configuration is used; values, errors and traces agree. -/
theorem evaluation_scoped_restate {V σ τ : Type} (p : Program) (sem : Sem V σ)
    (cfg : Config) (hc : cfg.checkOverlap = false) (project : τ → σ)
    (ctor : Term → List V → τ → ExtResult (V × τ))
    (extract : Term → V → τ → ExtResult (List V)) (allowed : TermId → Prop)
    (hscope : ProjectionScope p sem project ctor allowed)
    (hextract : ∀ t v st, extract t v st = sem.extract t v (project st)) (n : Nat) :
    EvaluationScopedProjects p sem cfg project ctor extract allowed n := by
  induction n with
  | zero => constructor <;> intros <;> exact scoped_throw project .outOfFuel
  | succ n ih =>
    constructor
    · intro e env hs
      cases e with
      | var ty x =>
        rw [evalExpr.eq_2, evalExpr.eq_2]
        split <;> first | exact scoped_pure project _ | exact scoped_throw project _
      | constBool ty b => exact scoped_pure project _
      | constInt ty i => exact scoped_pure project _
      | constPrim ty name =>
        rw [evalExpr.eq_5, evalExpr.eq_5]
        dsimp only [Sem.restate]
        split <;> first | exact scoped_pure project _ | exact scoped_throw project _
      | «let» ty bs body =>
        rw [evalExpr.eq_6, evalExpr.eq_6]
        apply scoped_bind_all project (ih.binds bs env (fun t ht => hs t (List.mem_append_left _ ht)))
        intro result
        cases result with
        | none => exact scoped_pure project _
        | some env' => exact ih.expr body env' (fun t ht => hs t (List.mem_append_right _ ht))
      | term ty t es =>
        rw [evalExpr.eq_7, evalExpr.eq_7]
        apply scoped_bind_all project (ih.args es env (fun u hu => hs u (List.mem_cons_of_mem _ hu)))
        intro result
        cases result with
        | none => exact scoped_pure project _
        | some vs => exact ih.term ty t vs (hs t (List.mem_cons_self ..))
    · intro es env hs
      cases es with
      | nil => exact scoped_pure project _
      | cons e es =>
        rw [evalArgs.eq_3, evalArgs.eq_3]
        apply scoped_bind_all project (ih.expr e env (fun t ht => hs t (List.mem_append_left _ ht)))
        intro result
        cases result with
        | none => exact scoped_pure project _
        | some v =>
          dsimp only
          apply scoped_bind_all project (ih.args es env (fun t ht => hs t (List.mem_append_right _ ht)))
          intro result
          cases result <;> exact scoped_pure project _
    · intro bs env hs
      cases bs with
      | nil => exact scoped_pure project _
      | cons b bs =>
        rcases b with ⟨x, ty, e⟩
        rw [evalBinds.eq_3, evalBinds.eq_3]
        apply scoped_bind_all project (ih.expr e env (fun t ht => hs t (List.mem_append_left _ ht)))
        intro result
        cases result with
        | none => exact scoped_pure project _
        | some v =>
          dsimp only
          split
          · exact ih.binds bs (env.set! x (some v)) (fun t ht => hs t (List.mem_append_right _ ht))
          · exact scoped_throw project _
    · intro ty t vs hs
      rw [applyTerm.eq_2, applyTerm.eq_2]
      apply scoped_bind project (scoped_lift project (termOf p t))
      intro initial trace term next tr hterm
      have ht : termOf p t = .ok term := by
        cases he : termOf p t with
        | error e => rw [he] at hterm; cases hterm
        | ok actual =>
          rw [he] at hterm
          simp only [M.run_liftM_ok, Except.ok.injEq, Prod.mk.injEq] at hterm
          exact congrArg Except.ok hterm.1
      have hsame : next = initial ∧ tr = trace := by
        rw [ht] at hterm
        simp only [M.run_liftM_ok, Except.ok.injEq, Prod.mk.injEq] at hterm
        exact ⟨hterm.2.1.symm, hterm.2.2.symm⟩
      rcases hsame with ⟨rfl, rfl⟩
      have hpj : Projects project
          (match term.kind with
          | .enumVariant k => pure (some ((sem.restate ctor extract).mkData ty k vs))
          | .struct => pure (some ((sem.restate ctor extract).mkData ty 0 vs))
          | .decl flags (some (.external _)) _ =>
            if flags.isMulti then throw (.unsupported s!"multi constructor {term.name}") else
            do let (st, tr) ← get
               match ctor term vs st with
               | .ok (v, st') => do set (st', tr); pure (some v)
               | .fail => if flags.isPartial then pure none else throw (.infallibleFailed term.name)
               | .unmodeled w => throw (.unmodeled w)
          | .decl flags (some .internal) _ =>
            if flags.isMulti then throw (.unsupported s!"multi constructor {term.name}") else
            do match ← selectRule p (sem.restate ctor extract) cfg n term (p.rulesOf t) vs with
               | none => if flags.isPartial then pure none else throw (.noRule term.name)
               | some (r, env) => do
                 match ← evalExpr p (sem.restate ctor extract) cfg n r.rhs env with
                 | some v => do fire r.id; pure (some v)
                 | none => pure none
          | _ => throw (.malformed s!"term {term.name} has no constructor"))
          (match term.kind with
          | .enumVariant k => pure (some (sem.mkData ty k vs))
          | .struct => pure (some (sem.mkData ty 0 vs))
          | .decl flags (some (.external _)) _ =>
            if flags.isMulti then throw (.unsupported s!"multi constructor {term.name}") else
            do let (st, tr) ← get
               match sem.ctor term vs st with
               | .ok (v, st') => do set (st', tr); pure (some v)
               | .fail => if flags.isPartial then pure none else throw (.infallibleFailed term.name)
               | .unmodeled w => throw (.unmodeled w)
          | .decl flags (some .internal) _ =>
            if flags.isMulti then throw (.unsupported s!"multi constructor {term.name}") else
            do match ← selectRule p sem cfg n term (p.rulesOf t) vs with
               | none => if flags.isPartial then pure none else throw (.noRule term.name)
               | some (r, env) => do
                 match ← evalExpr p sem cfg n r.rhs env with
                 | some v => do fire r.id; pure (some v)
                 | none => pure none
          | _ => throw (.malformed s!"term {term.name} has no constructor")) := by
        cases hk : term.kind <;> try dsimp only
        · exact scoped_pure project _
        · exact scoped_pure project _
        · rename_i flags c ex
          cases c with
          | none => exact scoped_throw project _
          | some c =>
            cases c with
            | external name =>
              dsimp only
              split
              · exact scoped_throw project _
              · apply scoped_get project
                intro st tr
                dsimp only [Sem.restate]
                have hc := hscope.ctor t term hs ht vs st
                cases he : ctor term vs st with
                | ok a =>
                  rcases a with ⟨v, next⟩
                  simp only [he, projectCtor] at hc
                  rw [← hc]
                  dsimp only
                  exact scoped_bind_all project (scoped_set project next tr) (fun _ => scoped_pure project _)
                | fail =>
                  simp only [he, projectCtor] at hc
                  rw [← hc]
                  dsimp only
                  split <;> first | exact scoped_pure project _ | exact scoped_throw project _
                | unmodeled w =>
                  simp only [he, projectCtor] at hc
                  rw [← hc]
                  exact scoped_throw project _
            | internal =>
              dsimp only
              split
              · exact scoped_throw project _
              · have hrules := hscope.rules t term hs ht flags ex hk
                apply scoped_bind project (ih.select term (p.rulesOf t) vs hrules)
                intro start trace result next tr hselect
                cases result with
                | none =>
                  dsimp only
                  split <;> first | exact scoped_pure project _ _ _ | exact scoped_throw project _ _ _
                | some pair =>
                  rcases pair with ⟨r, env⟩
                  have hr := (selectRule_some hc hselect).1
                  have he := (hrules r hr).2
                  have hbody : Projects project
                      (do match ← evalExpr p (sem.restate ctor extract) cfg n r.rhs env with
                          | some v => do fire r.id; pure (some v)
                          | none => pure none)
                      (do match ← evalExpr p sem cfg n r.rhs env with
                          | some v => do fire r.id; pure (some v)
                          | none => pure none) := by
                    apply scoped_bind_all project (ih.expr r.rhs env he)
                    intro result
                    cases result with
                    | none => exact scoped_pure project _
                    | some v =>
                      exact scoped_bind_all project (scoped_fire project r.id)
                        (fun _ => scoped_pure project _)
                  exact hbody next tr
      exact hpj _ _
    · intro r vs hs
      rw [matchRule.eq_2, matchRule.eq_2]
      apply scoped_get project
      intro st tr
      dsimp only
      rw [matchArgs_restate p sem project ctor extract hextract]
      apply scoped_bind_all project (scoped_lift project _)
      intro result
      cases result with
      | none => exact scoped_pure project _
      | some env => exact ih.iflets r.iflets env hs.1
    · intro ils env hs
      cases ils with
      | nil => exact scoped_pure project _
      | cons il ils =>
        rw [matchIfLets.eq_3, matchIfLets.eq_3]
        apply scoped_bind_all project (ih.expr il.rhs env (hs il (List.mem_cons_self ..)))
        intro result
        cases result with
        | none => exact scoped_pure project _
        | some v =>
          dsimp only
          apply scoped_get project
          intro st tr
          dsimp only
          rw [matchPat_restate p sem project ctor extract hextract]
          apply scoped_bind_all project (scoped_lift project _)
          intro result
          cases result with
          | none => exact scoped_pure project _
          | some env' => exact ih.iflets ils env' (fun q hq => hs q (List.mem_cons_of_mem _ hq))
    · intro r vs hs
      rw [tryRule.eq_2, tryRule.eq_2]
      apply scoped_get project
      intro st tr
      apply scoped_bind_all project (ih.rule r vs hs)
      intro result
      cases result with
      | some env => exact scoped_pure project _
      | none =>
        dsimp only
        exact scoped_bind_all project (scoped_set project st tr) (fun _ => scoped_pure project _)
    · intro term rs vs hs
      cases rs with
      | nil => exact scoped_pure project _
      | cons r rs =>
        rw [selectRule.eq_3, selectRule.eq_3]
        apply scoped_bind_all project (ih.tryRule r vs (hs r (List.mem_cons_self ..)))
        intro result
        cases result with
        | none => exact ih.select term rs vs (fun q hq => hs q (List.mem_cons_of_mem _ hq))
        | some env => simp only [hc, Bool.false_eq_true, ite_false]; exact scoped_pure project _

/-! Concrete rollback witness: a failed rule updates embedding state before its
pattern fails; the accepted rule observes the restored state and updates once.
Only handwritten toy rules are evaluated. -/

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

theorem evaluation_scoped_restate_witness :
    projectResult Prod.fst
      ((applyTerm ProjectionWitness.program
        (ProjectionWitness.sem.restate ProjectionWitness.ctor ProjectionWitness.extract)
        {} 100 0 0 [7]).run ((10, 0), #[])) =
      (applyTerm ProjectionWitness.program ProjectionWitness.sem {} 100 0 0 [7]).run (10, #[]) ∧
    (applyTerm ProjectionWitness.program
      (ProjectionWitness.sem.restate ProjectionWitness.ctor ProjectionWitness.extract)
      {} 100 0 0 [7]).run ((10, 0), #[]) = .ok (some 7, (11, 1), #[1]) :=
  ⟨(evaluation_scoped_restate _ _ {} rfl Prod.fst _ _ _ witness_scope
    (fun _ _ _ => rfl) 100).term 0 0 [7] (Or.inl rfl) (10, 0) #[], rfl⟩

end Isle.Interp
