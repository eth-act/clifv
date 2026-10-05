import FV.Backend.Proof.SpillCtlPipe
import FV.Backend.Proof.IselCovSound

/-!
# Control shapes of the ISLE lowering (V4): the state invariant, hand-checked rules, totality

* `ShpIs N s0 s`: every control form emitted since `s0` has its shape `CtlShape N`, and the
  vreg counter is at least `N`: the state invariant of the control-shape analysis.
* `HandOk ctx N vs rl`: root rule `rl` (matched against `vs`) keeps `ShpIs N s0` (the root rules
  the abstract interpreter does not check: calls, `try_call`s, `br_table`).
* `totalE`/`totalProg`: no expression calls a `partial` term; with `totalProg`, the
  right-hand side of a non-`partial` term never evaluates to `none` (`IselShpTotal`).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64

/-- **The state invariant** of the control-shape analysis. -/
def ShpIs (N : Nat) (s0 s : LState) : Prop := CtlSince N s0 s ∧ N ≤ s.nextVreg

/-- **A hand-checked root rule**: whenever `rl` matches `vs` (from a state with the invariant)
and its right-hand side runs, the invariant holds after it. -/
def HandOk (ctx : Ctx) (N : Nat) (vs : List V) (rl : Rule) : Prop :=
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (s0 s : LState) (tr : Array RuleId) (env : Isle.Interp.Env V)
    (s1 : LState × Array RuleId) (r : Option V) (s2 : LState) (tr2 : Array RuleId),
    1000 ≤ m → 1000 ≤ n → ShpIs N s0 s →
    (matchRule program (sem ctx) cfg m rl vs).run (s, tr) = .ok (some env, s1) →
    (evalExpr program (sem ctx) cfg n rl.rhs env).run s1 = .ok (r, (s2, tr2)) →
    ShpIs N s0 s2

/-- **A sub-run the abstract interpreter vouches for** (`aApply` of `t` on `as` gives `out`):
every run of `t` on arguments `as` describes, from a state with the invariant, keeps it and
returns a value `out` describes (discharged from the table in `IselShpDriver`). -/
def SubOk (f : Clif.Function) (ctx : Ctx) (N : Nat) (t : TermId) (as : List AW) (out : AW) :
    Prop :=
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (n : Nat) (ty : TypeId) (vs : List V) (s0 s : LState) (tr : Array RuleId) (r : Option V)
    (s' : LState) (tr' : Array RuleId),
    Holds2 f ctx as vs → ShpIs N s0 s →
    (applyTerm program (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    ShpIs N s0 s' ∧ ∀ v, r = some v → γ f ctx out v

/-! ## Totality -/

/-- A call of term `t` is total: `t` is not `partial`. -/
def termTotal (p : Program) (t : TermId) : Bool :=
  match termOf p t with
  | .ok term =>
    match term.kind with
    | .decl flags _ _ => !flags.isPartial
    | _ => true
  | .error _ => true

mutual
/-- No call of a `partial` term in the expression. -/
def totalE (p : Program) : Isle.Expr → Bool
  | .term _ t args => termTotal p t && totalL p args
  | .let _ bs body => totalB p bs && totalE p body
  | _ => true
/-- `totalE` of a list. -/
def totalL (p : Program) : List Isle.Expr → Bool
  | [] => true
  | e :: es => totalE p e && totalL p es
/-- `totalE` of `let*` bindings. -/
def totalB (p : Program) : List (VarId × TypeId × Isle.Expr) → Bool
  | [] => true
  | (_, _, e) :: bs => totalE p e && totalB p bs
end

/-- Term `t` has an internal constructor and is not `partial`. -/
def internalTotal (p : Program) (t : TermId) : Bool :=
  match termOf p t with
  | .ok term =>
    match term.kind with
    | .decl flags (some .internal) _ => !flags.isPartial
    | _ => false
  | .error _ => false

/-- **Every rule of every non-`partial` internal term has a total right-hand side.** -/
def totalProg (p : Program) : Bool :=
  (List.range p.ruleLists.size).all fun t =>
    !internalTotal p t || (p.rulesOf t).all fun r => totalE p r.rhs

/-- **Totality** (proven in `IselShpTotal`): a total expression, or a call of a non-`partial`
term, that does not throw returns a value. -/
def Totality : Prop :=
  (∀ (ctx : Ctx) (cfg : Config) (n : Nat) (e : Isle.Expr) (env : Isle.Interp.Env V)
    (s : LState × Array RuleId) (r : Option V) (s' : LState × Array RuleId),
    totalE program e = true → (evalExpr program (sem ctx) cfg n e env).run s = .ok (r, s') →
    r.isSome = true) ∧
  (∀ (ctx : Ctx) (cfg : Config) (n : Nat) (ty : TypeId) (t : TermId) (vs : List V)
    (s : LState × Array RuleId) (r : Option V) (s' : LState × Array RuleId),
    termTotal program t = true → (applyTerm program (sem ctx) cfg n ty t vs).run s = .ok (r, s') →
    r.isSome = true)

end Backend.Proof.Cov
