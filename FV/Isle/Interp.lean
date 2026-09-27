import FV.Isle.Syntax

/-!
# A generic ISLE rule interpreter

`Isle.Interp.run p sem cfg term args st` evaluates the internal constructor `term` of the ISLE
program `p` (exported data, `FV/Isle/Syntax.lean`) on argument values `args`, following the
execution model of the Rust code `cranelift-isle` generates
(`cranelift/isle/docs/language-reference.md`, "ISLE to Rust"; `cranelift-isle` `trie_again.rs`,
`codegen.rs`):

* **Rule selection.** The rules of a term are tried in descending priority. Within one
  priority, `cranelift-isle`'s overlap check rejects any two rules that may both match, so at
  most one can; the interpreter tries them in source order and, with `cfg.checkOverlap`,
  verifies the rest of the class does not also match (`Err.ambiguous`).
* **Match phase.** A rule matches if its argument patterns match and then each `if-let`, in
  order, evaluates its expression (which may call pure, possibly `partial`, constructors;
  failure means "rule does not match") and matches its pattern. Extern extractors are fallible
  unless declared infallible. The match phase has no effect on the embedding state: after a
  failed attempt the state is restored.
* **Commit.** The first matching rule is committed; its right-hand side is evaluated
  left-to-right, innermost first (`sema::Expr::visit` order), threading the state through extern
  constructors. A `partial` constructor failing on the right-hand side makes the whole term
  fail (the generated `?`), with no backtracking into other rules.
* **No rule.** A `partial` term returns `none`; a total term is an error (`Err.noRule`,
  the generated `unreachable!` panic).
* **Trace.** Each committed rule whose right-hand side succeeds is appended to the trace
  *after* its right-hand side ran (post-order), which is exactly where Cranelift's generated
  code emits its `trace-log` line (`log::debug!("ISLE {term} {file} line {n}")`).
* **Multi terms** (`decl multi`) are unsupported (`Err.unsupported`); the aarch64 unit has none.
* **Fuel.** Every expression node and term application costs one unit (`Err.outOfFuel`).

The interpreter is independent of CLIF and Arm: values `V`, the embedding state `σ`, and the
meaning of extern constructors/extractors and constants are supplied by `Sem V σ`.
-/

namespace Isle

/-- Result of an extern Rust function modelled in Lean. -/
inductive ExtResult (α : Type) where
  | ok (a : α)
  /-- A fallible function returned `None`. -/
  | fail
  /-- The embedding does not model this call; interpretation aborts. -/
  | unmodeled (what : String)
  deriving Repr, Inhabited

/-- Semantics of the embedding (the Rust `Context` implementation, types and constants). -/
structure Sem (V σ : Type) where
  /-- Integer literal of the ISLE type `ty`. -/
  int : TypeId → Int → V
  /-- Boolean literal. -/
  bool : Bool → V
  /-- Extern constant `$name` of type `ty` (`none`: unmodeled). -/
  prim : TypeId → String → Option V
  /-- Value equality, for repeated variables and constant patterns. -/
  eq : V → V → Bool
  /-- Build variant number `k` of the enum type `ty` (`k = 0` for a struct type) from fields. -/
  mkData : TypeId → Nat → List V → V
  /-- Destructure a value of the enum/struct type `ty` into its variant number and fields
  (`none`: the value is not of that type, which is an error). -/
  unData : TypeId → V → Option (Nat × List V)
  /-- Extern constructor of `term` on `args`. -/
  ctor : Term → List V → σ → ExtResult (V × σ)
  /-- Extern extractor of `term`: the input value to the term's argument values. -/
  extract : Term → V → σ → ExtResult (List V)

/-- Interpretation errors (as opposed to "no rule matched" of a partial term, which is a
`none` result). -/
inductive Err where
  | unmodeled (what : String)
  | outOfFuel
  /-- No rule of a total term matched (the generated code panics). -/
  | noRule (term : String)
  /-- Two rules of the same priority matched (`Config.checkOverlap`). -/
  | ambiguous (term : String) (rules : List String)
  /-- An extern extractor declared infallible, or a total extern constructor, failed. -/
  | infallibleFailed (term : String)
  | unsupported (what : String)
  /-- Ill-formed program or values (type confusion, unbound variable, arity mismatch). -/
  | malformed (msg : String)
  deriving Repr, DecidableEq, Inhabited

structure Config where
  /-- Also check that no other rule of the chosen rule's priority matches. -/
  checkOverlap : Bool := false
  fuel : Nat := 1000000
  deriving Repr, Inhabited

namespace Interp

/-- Variable environment of a rule, indexed by `VarId`. -/
abbrev Env (V : Type) := Array (Option V)

/-- Interpreter monad: embedding state and trace of fired rule ids. -/
abbrev M (σ : Type) := StateT (σ × Array RuleId) (Except Err)

variable {V σ : Type} (p : Program) (sem : Sem V σ) (cfg : Config)

def termOf (t : TermId) : Except Err Term :=
  match p.term? t with
  | some term => pure term
  | none => throw (.malformed s!"unknown term {t}")

mutual
/-- Match `pat` against `v`, extending `env`; `none` if it does not match. -/
def matchPat (st : σ) : Pattern → V → Env V → Except Err (Option (Env V))
  | .bind _ x sub, v, env =>
    if x < env.size then matchPat st sub v (env.set! x (some v))
    else throw (.malformed s!"variable {x} out of range")
  | .var _ x, v, env =>
    match env[x]? with
    | some (some w) => pure (if sem.eq v w then some env else none)
    | _ => throw (.malformed s!"unbound variable {x}")
  | .constBool _ b, v, env => pure (if sem.eq v (sem.bool b) then some env else none)
  | .constInt ty i, v, env => pure (if sem.eq v (sem.int ty i) then some env else none)
  | .constPrim ty n, v, env =>
    match sem.prim ty n with
    | some c => pure (if sem.eq v c then some env else none)
    | none => throw (.unmodeled s!"constant ${n}")
  | .wildcard _, _, env => pure (some env)
  | .and _ ps, v, env => matchAll st ps v env
  | .term ty t args, v, env => do
    let term ← termOf p t
    match term.kind with
    | .enumVariant k =>
      match sem.unData ty v with
      | some (k', fs) => if k == k' then matchArgs st args fs env else pure none
      | none => throw (.malformed s!"value is not of type {p.typeName ty} (term {term.name})")
    | .struct =>
      match sem.unData ty v with
      | some (_, fs) => matchArgs st args fs env
      | none => throw (.malformed s!"value is not of type {p.typeName ty} (term {term.name})")
    | .decl flags _ (some (.external _ infallible)) =>
      if flags.isMulti then throw (.unsupported s!"multi extractor {term.name}") else
      match sem.extract term v st with
      | .ok fs => matchArgs st args fs env
      | .fail => if infallible then throw (.infallibleFailed term.name) else pure none
      | .unmodeled w => throw (.unmodeled w)
    | _ => throw (.malformed s!"term {term.name} has no extern extractor (unexpanded pattern)")
/-- Match every pattern against the same value (`and`). -/
def matchAll (st : σ) : List Pattern → V → Env V → Except Err (Option (Env V))
  | [], _, env => pure (some env)
  | q :: qs, v, env => do
    match ← matchPat st q v env with
    | some env' => matchAll st qs v env'
    | none => pure none
/-- Match patterns against values pointwise. -/
def matchArgs (st : σ) : List Pattern → List V → Env V → Except Err (Option (Env V))
  | [], [], env => pure (some env)
  | q :: qs, w :: ws, env => do
    match ← matchPat st q w env with
    | some env' => matchArgs st qs ws env'
    | none => pure none
  | _, _, _ => throw (.malformed "arity mismatch in pattern")
end

/-- Append a fired rule to the trace. -/
def fire (r : RuleId) : M σ Unit := modify fun (s, tr) => (s, tr.push r)

/-- The rules of one priority class starting at the head of `rs`, and the rest. -/
def splitClass (prio : Int) : List Rule → List Rule × List Rule
  | [] => ([], [])
  | r :: rs =>
    if r.prio == prio then
      let (a, b) := splitClass prio rs
      (r :: a, b)
    else ([], r :: rs)

mutual
/-- Evaluate an expression; `none` means a `partial` constructor failed. -/
def evalExpr : Nat → Expr → Env V → M σ (Option V)
  | 0, _, _ => throw .outOfFuel
  | _ + 1, .var _ x, env =>
    match env[x]? with
    | some (some v) => pure (some v)
    | _ => throw (.malformed s!"unbound variable {x}")
  | _ + 1, .constBool _ b, _ => pure (some (sem.bool b))
  | _ + 1, .constInt ty i, _ => pure (some (sem.int ty i))
  | _ + 1, .constPrim ty n, _ =>
    match sem.prim ty n with
    | some c => pure (some c)
    | none => throw (.unmodeled s!"constant ${n}")
  | n + 1, .let _ binds body, env => do
    match ← evalBinds n binds env with
    | some env' => evalExpr n body env'
    | none => pure none
  | n + 1, .term ty t args, env => do
    match ← evalArgs n args env with
    | some vs => applyTerm n ty t vs
    | none => pure none
/-- Evaluate arguments left to right. -/
def evalArgs : Nat → List Expr → Env V → M σ (Option (List V))
  | 0, _, _ => throw .outOfFuel
  | _ + 1, [], _ => pure (some [])
  | n + 1, e :: es, env => do
    match ← evalExpr n e env with
    | none => pure none
    | some v =>
      match ← evalArgs n es env with
      | some vs => pure (some (v :: vs))
      | none => pure none
/-- Evaluate `let*` bindings. -/
def evalBinds : Nat → List (VarId × TypeId × Expr) → Env V → M σ (Option (Env V))
  | 0, _, _ => throw .outOfFuel
  | _ + 1, [], env => pure (some env)
  | n + 1, (x, _, e) :: bs, env => do
    match ← evalExpr n e env with
    | none => pure none
    | some v =>
      if x < env.size then evalBinds n bs (env.set! x (some v))
      else throw (.malformed s!"variable {x} out of range")
/-- Apply the constructor of term `t` (result type `ty`) to values. -/
def applyTerm : Nat → TypeId → TermId → List V → M σ (Option V)
  | 0, _, _, _ => throw .outOfFuel
  | n + 1, ty, t, vs => do
    let term ← termOf p t
    match term.kind with
    | .enumVariant k => pure (some (sem.mkData ty k vs))
    | .struct => pure (some (sem.mkData ty 0 vs))
    | .decl flags (some (.external _)) _ =>
      if flags.isMulti then throw (.unsupported s!"multi constructor {term.name}") else
      let (st, tr) ← get
      match sem.ctor term vs st with
      | .ok (v, st') => do set (st', tr); pure (some v)
      | .fail => if flags.isPartial then pure none else throw (.infallibleFailed term.name)
      | .unmodeled w => throw (.unmodeled w)
    | .decl flags (some .internal) _ =>
      if flags.isMulti then throw (.unsupported s!"multi constructor {term.name}") else
      match ← selectRule n term (p.rulesOf t) vs with
      | none => if flags.isPartial then pure none else throw (.noRule term.name)
      | some (r, env) => do
        match ← evalExpr n r.rhs env with
        | some v => do fire r.id; pure (some v)
        | none => pure none
    | _ => throw (.malformed s!"term {term.name} has no constructor")
/-- Match phase of one rule: argument patterns, then the if-lets. -/
def matchRule : Nat → Rule → List V → M σ (Option (Env V))
  | 0, _, _ => throw .outOfFuel
  | n + 1, r, vs => do
    let (st, _) ← get
    match ← matchArgs p sem st r.args vs (Array.replicate r.vars.length none) with
    | none => pure none
    | some env => matchIfLets n r.iflets env
def matchIfLets : Nat → List IfLet → Env V → M σ (Option (Env V))
  | 0, _, _ => throw .outOfFuel
  | _ + 1, [], env => pure (some env)
  | n + 1, il :: ils, env => do
    match ← evalExpr n il.rhs env with
    | none => pure none
    | some v =>
      let (st, _) ← get
      match ← matchPat p sem st il.lhs v env with
      | none => pure none
      | some env' => matchIfLets n ils env'
/-- Try one rule; on failure restore the state (the match phase is pure). -/
def tryRule : Nat → Rule → List V → M σ (Option (Env V))
  | 0, _, _ => throw .outOfFuel
  | n + 1, r, vs => do
    let saved ← get
    match ← matchRule n r vs with
    | some env => pure (some env)
    | none => do set saved; pure none
/-- Rules of the same priority as a chosen rule that also match (for `checkOverlap`). -/
def alsoMatching : Nat → List Rule → List V → M σ (List String)
  | 0, _, _ => throw .outOfFuel
  | _ + 1, [], _ => pure []
  | n + 1, r :: rs, vs => do
    let saved ← get
    let m ← matchRule n r vs
    set saved
    let rest ← alsoMatching n rs vs
    pure (if m.isSome then r.name :: rest else rest)
/-- The first matching rule in `ruleBefore` order. -/
def selectRule : Nat → Term → List Rule → List V → M σ (Option (Rule × Env V))
  | 0, _, _, _ => throw .outOfFuel
  | _ + 1, _, [], _ => pure none
  | n + 1, term, r :: rs, vs => do
    match ← tryRule n r vs with
    | none => selectRule n term rs vs
    | some env =>
      if cfg.checkOverlap then do
        let sameClass := (splitClass r.prio rs).1
        let others ← alsoMatching n sameClass vs
        if others.isEmpty then pure (some (r, env))
        else throw (.ambiguous term.name (r.name :: others))
      else pure (some (r, env))
end

end Interp

/-- Result of interpreting a term: its value (`none`: a partial term failed), the final
embedding state, and the fired rules in Cranelift `trace-log` order. -/
structure RunResult (V σ : Type) where
  value : Option V
  state : σ
  trace : List RuleId

/-- Interpret the constructor of the term named `term` on `args` from state `st`. -/
def Interp.run {V σ : Type} (p : Program) (sem : Sem V σ) (cfg : Config) (term : String)
    (args : List V) (st : σ) : Except Err (RunResult V σ) := do
  let some t := p.termByName? term | throw (.malformed s!"unknown term {term}")
  let (v, st', tr) ← (Interp.applyTerm p sem cfg cfg.fuel t.ret t.id args).run (st, #[])
  pure ⟨v, st', tr.toList⟩

/-- Names of traced rules. -/
def Program.ruleNames (p : Program) (ids : List RuleId) : List String :=
  ids.map fun r => (p.rule? r).elim s!"<rule {r}>" (·.name)

end Isle
