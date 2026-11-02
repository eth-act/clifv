import FV.Isle.Interp

/-!
State transport for the single-result ISLE interpreter. A lowering driver may
add scheduling bookkeeping without changing ISLE values or pure operations.
Extractors must agree after projecting that bookkeeping; constructor agreement
is needed separately when transporting evaluation. No generated program is
unfolded by these proofs.
-/

namespace Isle

/-- Keep the value operations of an embedding while replacing its state. -/
def Sem.restate {V σ τ : Type} (sem : Sem V σ)
    (ctor : Term → List V → τ → ExtResult (V × τ))
    (extract : Term → V → τ → ExtResult (List V)) : Sem V τ where
  int := sem.int
  bool := sem.bool
  prim := sem.prim
  eq := sem.eq
  mkData := sem.mkData
  unData := sem.unData
  ctor := ctor
  extract := extract

namespace Interp

section Patterns

variable {V σ τ : Type} (p : Program) (sem : Sem V σ) (project : τ → σ)
  (ctor : Term → List V → τ → ExtResult (V × τ))
  (extract : Term → V → τ → ExtResult (List V))

mutual
/-- Pattern matching reads the projected embedding state and has the same
success, failure, error and bindings after adding bookkeeping. -/
theorem matchPat_restate
    (hextract : ∀ t v st, extract t v st = sem.extract t v (project st)) (st : τ) (pat : Pattern) (v : V) (env : Env V) :
    matchPat p (sem.restate ctor extract) st pat v env =
      matchPat p sem (project st) pat v env := by
  cases pat with
  | bind ty x sub =>
    simp only [matchPat, Sem.restate]
    split
    · exact matchPat_restate hextract st sub v (env.set! x (some v))
    · rfl
  | var ty x => rfl
  | constBool ty b => rfl
  | constInt ty i => rfl
  | constPrim ty n => rfl
  | wildcard ty => rfl
  | and ty ps =>
    exact matchAll_restate hextract st ps v env
  | term ty t args =>
    simp only [matchPat, Sem.restate]
    congr 1
    funext term
    cases term.kind <;> try dsimp only
    · split
      · split
        · exact matchArgs_restate hextract st args _ env
        · rfl
      · rfl
    · split
      · exact matchArgs_restate hextract st args _ env
      · rfl
    · rename_i flags c e
      cases e with
      | none => rfl
      | some ext =>
        cases ext with
        | internal form => rfl
        | external fn infallible =>
          dsimp only
          split
          · rfl
          · rw [hextract]
            split
            · exact matchArgs_restate hextract st args _ env
            · rfl
            · rfl
termination_by sizeOf pat

/-- State transport for conjunctions of patterns. -/
theorem matchAll_restate
    (hextract : ∀ t v st, extract t v st = sem.extract t v (project st)) (st : τ) (ps : List Pattern) (v : V) (env : Env V) :
    matchAll p (sem.restate ctor extract) st ps v env =
      matchAll p sem (project st) ps v env := by
  cases ps with
  | nil => rfl
  | cons q qs =>
    rw [matchAll, matchAll, matchPat_restate hextract st q v env]
    congr 1
    funext result
    cases result with
    | none => rfl
    | some env' => exact matchAll_restate hextract st qs v env'
termination_by sizeOf ps

/-- State transport for argument patterns. -/
theorem matchArgs_restate
    (hextract : ∀ t v st, extract t v st = sem.extract t v (project st)) (st : τ) (ps : List Pattern) (vs : List V) (env : Env V) :
    matchArgs p (sem.restate ctor extract) st ps vs env =
      matchArgs p sem (project st) ps vs env := by
  cases ps with
  | nil => cases vs <;> rfl
  | cons q qs =>
    cases vs with
    | nil => rfl
    | cons v vs =>
      rw [matchArgs, matchArgs, matchPat_restate hextract st q v env]
      congr 1
      funext result
      cases result with
      | none => rfl
      | some env' => exact matchArgs_restate hextract st qs vs env'
termination_by sizeOf ps
end

end Patterns

/-- Project the state of a monadic result, retaining errors, values and trace. -/
def projectResult {σ τ α : Type} (project : τ → σ) :
    Except Err (α × (τ × Array RuleId)) → Except Err (α × (σ × Array RuleId))
  | .error e => .error e
  | .ok (a, st, tr) => .ok (a, project st, tr)

/-- Equality of computations after forgetting added embedding state. -/
def Projects {σ τ α : Type} (project : τ → σ) (x : M τ α) (y : M σ α) : Prop :=
  ∀ st tr, projectResult project (x.run (st, tr)) = y.run (project st, tr)

private theorem projects_pure {σ τ α : Type} (project : τ → σ) (a : α) :
    Projects project (pure a) (pure a) := by intro st tr; rfl

private theorem projects_throw {σ τ α : Type} (project : τ → σ) (err : Err) :
    Projects project (throw err : M τ α) (throw err) := by intro st tr; rfl

private theorem projects_lift {σ τ α : Type} (project : τ → σ) (x : Except Err α) :
    Projects project (liftM x) (liftM x) := by
  intro st tr
  cases x <;> rfl

private theorem projects_bind {σ τ α β : Type} (project : τ → σ)
    {x : M τ α} {y : M σ α} {f : α → M τ β} {g : α → M σ β}
    (hx : Projects project x y) (hf : ∀ a, Projects project (f a) (g a)) :
    Projects project (x >>= f) (y >>= g) := by
  intro st tr
  have h := hx st tr
  change projectResult project (x.run (st, tr) >>= fun a => (f a.1).run a.2) =
    (y.run (project st, tr) >>= fun a => (g a.1).run a.2)
  cases he : x.run (st, tr) with
  | error e =>
    simp only [he, projectResult] at h
    rw [← h]
    rfl
  | ok a =>
    rcases a with ⟨a, next, trace⟩
    simp only [he, projectResult] at h
    rw [← h]
    exact hf a next trace

private theorem projects_get_bind {σ τ α : Type} (project : τ → σ)
    {f : (τ × Array RuleId) → M τ α} {g : (σ × Array RuleId) → M σ α}
    (hf : ∀ st tr, Projects project (f (st, tr)) (g (project st, tr))) :
    Projects project (get >>= f) (get >>= g) := by
  intro st tr
  exact hf st tr st tr

private theorem projects_set {σ τ : Type} (project : τ → σ) (st : τ)
    (tr : Array RuleId) : Projects project (set (st, tr)) (set (project st, tr)) := by
  intro initial trace
  rfl

private theorem projects_fire {σ τ : Type} (project : τ → σ) (r : RuleId) :
    Projects project (fire r) (fire r) := by intro st tr; rfl

/-- Forget bookkeeping in a constructor's successful state update. -/
def projectCtor {V σ τ : Type} (project : τ → σ) :
    ExtResult (V × τ) → ExtResult (V × σ)
  | .ok (v, st) => .ok (v, project st)
  | .fail => .fail
  | .unmodeled s => .unmodeled s

/-- Simultaneous fuel invariant, including failed rule rollback and overlap
checking as well as expression evaluation. -/
structure EvaluationProjects {V σ τ : Type} (p : Program) (sem : Sem V σ)
    (cfg : Config) (project : τ → σ)
    (ctor : Term → List V → τ → ExtResult (V × τ))
    (extract : Term → V → τ → ExtResult (List V)) (n : Nat) : Prop where
  expr : ∀ e env, Projects project (evalExpr p (sem.restate ctor extract) cfg n e env)
    (evalExpr p sem cfg n e env)
  args : ∀ es env, Projects project (evalArgs p (sem.restate ctor extract) cfg n es env)
    (evalArgs p sem cfg n es env)
  binds : ∀ bs env, Projects project (evalBinds p (sem.restate ctor extract) cfg n bs env)
    (evalBinds p sem cfg n bs env)
  term : ∀ ty t vs, Projects project (applyTerm p (sem.restate ctor extract) cfg n ty t vs)
    (applyTerm p sem cfg n ty t vs)
  rule : ∀ r vs, Projects project (matchRule p (sem.restate ctor extract) cfg n r vs)
    (matchRule p sem cfg n r vs)
  iflets : ∀ ils env, Projects project (matchIfLets p (sem.restate ctor extract) cfg n ils env)
    (matchIfLets p sem cfg n ils env)
  tryRule : ∀ r vs, Projects project (Interp.tryRule p (sem.restate ctor extract) cfg n r vs)
    (Interp.tryRule p sem cfg n r vs)
  others : ∀ rs vs, Projects project (alsoMatching p (sem.restate ctor extract) cfg n rs vs)
    (alsoMatching p sem cfg n rs vs)
  select : ∀ t rs vs, Projects project (selectRule p (sem.restate ctor extract) cfg n t rs vs)
    (selectRule p sem cfg n t rs vs)

/-- If external calls commute with state projection, every interpreter phase
commutes with it at every fuel, including rollback, overlap errors and trace. -/
theorem evaluation_restate {V σ τ : Type} (p : Program) (sem : Sem V σ)
    (cfg : Config) (project : τ → σ)
    (ctor : Term → List V → τ → ExtResult (V × τ))
    (extract : Term → V → τ → ExtResult (List V))
    (hctor : ∀ t vs st, projectCtor project (ctor t vs st) = sem.ctor t vs (project st))
    (hextract : ∀ t v st, extract t v st = sem.extract t v (project st)) (n : Nat) :
    EvaluationProjects p sem cfg project ctor extract n := by
  induction n with
  | zero =>
    constructor <;> intros <;> exact projects_throw project .outOfFuel
  | succ n ih =>
    constructor
    · intro e env
      cases e with
      | var ty x =>
        rw [evalExpr.eq_2, evalExpr.eq_2]
        split <;> first | exact projects_pure project _ | exact projects_throw project _
      | constBool ty b => exact projects_pure project _
      | constInt ty i => exact projects_pure project _
      | constPrim ty name =>
        rw [evalExpr.eq_5, evalExpr.eq_5]
        dsimp only [Sem.restate]
        split <;> first | exact projects_pure project _ | exact projects_throw project _
      | «let» ty binds body =>
        rw [evalExpr.eq_6, evalExpr.eq_6]
        apply projects_bind project (ih.binds binds env)
        intro result
        cases result with
        | none => exact projects_pure project _
        | some env' => exact ih.expr body env'
      | term ty t args =>
        rw [evalExpr.eq_7, evalExpr.eq_7]
        apply projects_bind project (ih.args args env)
        intro result
        cases result with
        | none => exact projects_pure project _
        | some vs => exact ih.term ty t vs
    · intro es env
      cases es with
      | nil => exact projects_pure project _
      | cons e es =>
        rw [evalArgs.eq_3, evalArgs.eq_3]
        apply projects_bind project (ih.expr e env)
        intro result
        cases result with
        | none => exact projects_pure project _
        | some v =>
          try dsimp only
          apply projects_bind project (ih.args es env)
          intro result
          cases result <;> exact projects_pure project _
    · intro bs env
      cases bs with
      | nil => exact projects_pure project _
      | cons b bs =>
        rcases b with ⟨x, ty, e⟩
        rw [evalBinds.eq_3, evalBinds.eq_3]
        apply projects_bind project (ih.expr e env)
        intro result
        cases result with
        | none => exact projects_pure project _
        | some v =>
          try dsimp only
          split
          · exact ih.binds bs (env.set! x (some v))
          · exact projects_throw project _
    · intro ty t vs
      rw [applyTerm.eq_2, applyTerm.eq_2]
      apply projects_bind project (projects_lift project (termOf p t))
      intro term
      cases term.kind <;> try dsimp only
      · exact projects_pure project _
      · exact projects_pure project _
      · rename_i flags c ex
        cases c with
        | none => exact projects_throw project _
        | some c =>
          cases c with
          | external name =>
            dsimp only
            split
            · exact projects_throw project _
            · apply projects_get_bind project
              intro st tr
              dsimp only [Sem.restate]
              have hc := hctor term vs st
              cases he : ctor term vs st with
              | ok a =>
                rcases a with ⟨v, next⟩
                simp only [he, projectCtor] at hc
                rw [← hc]
                dsimp only
                exact projects_bind project (projects_set project next tr)
                  (fun _ => projects_pure project _)
              | fail =>
                simp only [he, projectCtor] at hc
                rw [← hc]
                dsimp only
                split
                · exact projects_pure project _
                · exact projects_throw project _
              | unmodeled w =>
                simp only [he, projectCtor] at hc
                rw [← hc]
                dsimp only
                exact projects_throw project _
          | internal =>
            dsimp only
            split
            · exact projects_throw project _
            · apply projects_bind project (ih.select term (p.rulesOf t) vs)
              intro result
              cases result with
              | none =>
                try dsimp only
                split
                · exact projects_pure project _
                · exact projects_throw project _
              | some pair =>
                try dsimp only
                rcases pair with ⟨r, env⟩
                apply projects_bind project (ih.expr r.rhs env)
                intro result
                cases result with
                | none => exact projects_pure project _
                | some v =>
                  try dsimp only
                  exact projects_bind project (projects_fire project r.id)
                    (fun _ => projects_pure project _)
    · intro r vs
      rw [matchRule.eq_2, matchRule.eq_2]
      apply projects_get_bind project
      intro st tr
      dsimp only
      rw [matchArgs_restate p sem project ctor extract hextract]
      apply projects_bind project (projects_lift project _)
      intro result
      cases result with
      | none => exact projects_pure project _
      | some env => exact ih.iflets r.iflets env
    · intro ils env
      cases ils with
      | nil => exact projects_pure project _
      | cons il ils =>
        rw [matchIfLets.eq_3, matchIfLets.eq_3]
        apply projects_bind project (ih.expr il.rhs env)
        intro result
        cases result with
        | none => exact projects_pure project _
        | some v =>
          try dsimp only
          apply projects_get_bind project
          intro st tr
          dsimp only
          rw [matchPat_restate p sem project ctor extract hextract]
          apply projects_bind project (projects_lift project _)
          intro result
          cases result with
          | none => exact projects_pure project _
          | some env' => exact ih.iflets ils env'
    · intro r vs
      rw [tryRule.eq_2, tryRule.eq_2]
      apply projects_get_bind project
      intro st tr
      apply projects_bind project (ih.rule r vs)
      intro result
      cases result with
      | some env => exact projects_pure project _
      | none =>
        dsimp only
        exact projects_bind project (projects_set project st tr)
          (fun _ => projects_pure project _)
    · intro rs vs
      cases rs with
      | nil => exact projects_pure project _
      | cons r rs =>
        rw [alsoMatching.eq_3, alsoMatching.eq_3]
        apply projects_get_bind project
        intro st tr
        apply projects_bind project (ih.rule r vs)
        intro result
        apply projects_bind project (projects_set project st tr)
        intro ignored
        exact projects_bind project (ih.others rs vs) (fun _ => projects_pure project _)
    · intro term rs vs
      cases rs with
      | nil => exact projects_pure project _
      | cons r rs =>
        rw [selectRule.eq_3, selectRule.eq_3]
        apply projects_bind project (ih.tryRule r vs)
        intro result
        cases result with
        | none => exact ih.select term rs vs
        | some env =>
          try dsimp only
          split
          · apply projects_bind project (ih.others (splitClass r.prio rs).1 vs)
            intro others
            split
            · exact projects_pure project _
            · exact projects_throw project _
          · exact projects_pure project _

/-- Project a completed interpreter invocation without losing its trace. -/
def projectRun {V σ τ : Type} (project : τ → σ) :
    Except Err (RunResult V τ) → Except Err (RunResult V σ)
  | .error e => .error e
  | .ok r => .ok ⟨r.value, project r.state, r.trace⟩

/-- The public interpreter agrees after forgetting added state. The agreement
premises concern external functions, not a checker on the compiled program. -/
theorem run_restate {V σ τ : Type} (p : Program) (sem : Sem V σ)
    (cfg : Config) (project : τ → σ)
    (ctor : Term → List V → τ → ExtResult (V × τ))
    (extract : Term → V → τ → ExtResult (List V))
    (hctor : ∀ t vs st, projectCtor project (ctor t vs st) = sem.ctor t vs (project st))
    (hextract : ∀ t v st, extract t v st = sem.extract t v (project st))
    (term : String) (args : List V) (st : τ) :
    projectRun project (run p (sem.restate ctor extract) cfg term args st) =
      run p sem cfg term args (project st) := by
  cases ht : p.termByName? term with
  | none => simp only [run, ht]; rfl
  | some t =>
    have hp := (evaluation_restate p sem cfg project ctor extract hctor hextract cfg.fuel).term
      t.ret t.id args st #[]
    simp only [run, ht]
    cases he : (applyTerm p (sem.restate ctor extract) cfg cfg.fuel t.ret t.id args).run
        (st, #[]) with
    | error e =>
      simp only [he, projectResult] at hp
      rw [← hp]
      rfl
    | ok a =>
      rcases a with ⟨v, next, tr⟩
      simp only [he, projectResult] at hp
      rw [← hp]
      rfl

/-! Non-vacuity: a small program with real external state updates. The first
rule updates state in an if-let and then fails its pattern. The successful rule
must see the restored state, update it once, and leave its id in the trace.
These are handwritten toy rules; no generated ISLE program is evaluated. -/

namespace ProjectionWitness

def tick : Term := { (default : Term) with
  id := 1
  name := "tick"
  args := [0]
  ret := 0
  kind := .decl ⟨false, false, false, false⟩ (some (.external "tick"))
    (some (.external "tick" false)) }

def root : Term := { (default : Term) with
  id := 0
  name := "root"
  args := [0]
  ret := 0
  kind := .decl ⟨false, false, false, false⟩ (some .internal) none }

def failed : Rule := { (default : Rule) with
  id := 0
  name := "failed"
  term := 0
  args := [.bind 0 0 (.wildcard 0)]
  vars := [("v", 0)]
  iflets := [⟨.constInt 0 99, .term 0 1 [.var 0 0]⟩]
  rhs := .var 0 0
  prio := 1 }

def accepted : Rule := { (default : Rule) with
  id := 1
  name := "accepted"
  term := 0
  args := [.bind 0 0 (.wildcard 0)]
  vars := [("v", 0)]
  rhs := .term 0 1 [.var 0 0] }

def program : Program := { (default : Program) with
  name := "state-projection-witness"
  terms := #[root, tick]
  rules := #[failed, accepted]
  ruleLists := #[[failed, accepted], []] }

def sem : Sem Nat Nat where
  int _ i := i.toNat
  bool b := if b then 1 else 0
  prim _ _ := none
  eq := (· == ·)
  mkData _ _ vs := vs.headD 0
  unData _ v := some (0, [v])
  ctor _ vs st := .ok (vs.headD 0, st + 1)
  extract _ v _ := .ok [v]

def ctor (_ : Term) (vs : List Nat) (st : Nat × Nat) : ExtResult (Nat × (Nat × Nat)) :=
  .ok (vs.headD 0, st.1 + 1, st.2 + 1)

def extract (_ : Term) (v : Nat) (_ : Nat × Nat) : ExtResult (List Nat) := .ok [v]

def cfg : Config := { checkOverlap := true, fuel := 100 }

def pat : Pattern := .and 0 [.term 0 1 [.constInt 0 7], .bind 0 0 (.wildcard 0)]

theorem matchPat_restate_witness :
    matchPat program (sem.restate ctor extract) (10, 0) pat 7 #[none] =
      matchPat program sem 10 pat 7 #[none] ∧
    matchPat program (sem.restate ctor extract) (10, 0) pat 7 #[none] =
      .ok (some #[some 7]) :=
  ⟨matchPat_restate program sem Prod.fst ctor extract (fun _ _ _ => rfl) _ _ _ _, rfl⟩

theorem matchAll_restate_witness :
    matchAll program (sem.restate ctor extract) (10, 0) [pat] 7 #[none] =
      matchAll program sem 10 [pat] 7 #[none] ∧
    matchAll program (sem.restate ctor extract) (10, 0) [pat] 7 #[none] =
      .ok (some #[some 7]) :=
  ⟨matchAll_restate program sem Prod.fst ctor extract (fun _ _ _ => rfl) _ _ _ _, rfl⟩

theorem matchArgs_restate_witness :
    matchArgs program (sem.restate ctor extract) (10, 0) [pat] [7] #[none] =
      matchArgs program sem 10 [pat] [7] #[none] ∧
    matchArgs program (sem.restate ctor extract) (10, 0) [pat] [7] #[none] =
      .ok (some #[some 7]) :=
  ⟨matchArgs_restate program sem Prod.fst ctor extract (fun _ _ _ => rfl) _ _ _ _, rfl⟩

theorem evaluation_restate_witness :
    (∀ t vs st, projectCtor Prod.fst (ctor t vs st) = sem.ctor t vs st.1) ∧
    (∀ t v st, extract t v st = sem.extract t v st.1) ∧
    EvaluationProjects program sem cfg Prod.fst ctor extract cfg.fuel ∧
    run program (sem.restate ctor extract) cfg "root" [7] (10, 0) =
      .ok ⟨some 7, (11, 1), [1]⟩ :=
  ⟨(fun _ _ _ => rfl), (fun _ _ _ => rfl),
    evaluation_restate program sem cfg Prod.fst ctor extract (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) _, rfl⟩

theorem run_restate_witness :
    projectRun Prod.fst (run program (sem.restate ctor extract) cfg "root" [7] (10, 0)) =
      run program sem cfg "root" [7] 10 ∧
    run program sem cfg "root" [7] 10 = .ok ⟨some 7, 11, [1]⟩ :=
  ⟨run_restate program sem cfg Prod.fst ctor extract (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) _ _ _, rfl⟩

end ProjectionWitness

end Interp
end Isle
