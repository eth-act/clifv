import FV.Backend.Proof.IselSzDefs
import FV.Backend.Proof.IselCovCheckT
import FV.Backend.Proof.IselCovSemT

/-!
# The size of the ISLE lowering's output over float-capable contexts: the cost analysis

The typed counterpart of `IselSzDefs`' cost machinery: `cIfLetsT`/`cRuleT`/`cRuleLeT`/`chkCostT`
are the cost of an if-let chain, a rule and the table check, over the typed pattern machinery
(`aPatT`/`aRuleEnvsT`, `IselCovCheckT`); `ExtWT`/`OracleWT` are `ExtW`/`OracleW` with `γLT`.
`HandW` and `cApply`/`cExpr`/`cArgs`/`cBinds` do not use the pattern checker and are
`IselSzDefs`'s.
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

section Eval
variable (p : Program) (tab : Tab) (aw : TermId → List AW → Option Nat) (ctab : CTab)
  (aext : TermId → AW → List AW)
  (actor : TermId → List AW → AW) (apre : TermId → List AW → Bool)
  (aOracle : TermId → List AW → Option AW)
  (iOps fOps : List Nat)

/-- The weight the if-lets emit, on every path of abstract environments (the maximum). -/
def cIfLetsT : List IfLet → List AW → Option Nat
  | [], _ => some 0
  | il :: ils, env =>
    match aExpr p tab actor apre aOracle il.rhs env, cExpr p tab aw ctab actor apre aOracle il.rhs env with
    | some a, some c =>
      match (aPatT p aext iOps fOps a il.lhs env).mapM fun e => cIfLetsT ils e with
      | some ds => some (c + ds.foldl max 0)
      | none => none
    | _, _ => none

/-- The weight a run of rule `r` on values `ins` describes emits: its if-lets (on every
environment of its argument patterns) and its right-hand side (on every environment after its
if-lets). -/
def cRuleT (ins : List AW) (r : Rule) : Option Nat :=
  match (aPatArgsT p aext iOps fOps ins r.args (List.replicate r.vars.length .top)).mapM
      (cIfLetsT p tab aw ctab aext actor apre aOracle iOps fOps r.iflets),
    aRuleEnvsT p tab aext actor apre aOracle iOps fOps ins r with
  | some cs, some envs =>
    match envs.mapM (cExpr p tab aw ctab actor apre aOracle r.rhs) with
    | some ds => some (cs.foldl max 0 + ds.foldl max 0)
    | none => none
  | _, _ => none

/-- Rule `r` on values `ins` emits at most weight `c`. -/
def cRuleLeT (ins : List AW) (c : Nat) (r : Rule) : Bool :=
  match cRuleT p tab aw ctab aext actor apre aOracle iOps fOps ins r with
  | some c' => decide (c' ≤ c)
  | none => false

/-- Every rule of every entry of the cost table emits at most the entry's weight. -/
def chkCostT : Bool :=
  ctab.all fun e => (p.rulesOf e.1).all
    (cRuleLeT p tab aw ctab aext actor apre aOracle iOps fOps e.2.1 e.2.2)

end Eval

/-! ## The facts the soundness of the cost analysis assumes -/

/-- **Extern constructors** emit at most their cost, over float-capable contexts. -/
def ExtWT (S : Clif.Inst → Bool) (iOps fOps : List Nat) (f : Clif.Function) (ctx : Ctx)
    (apre : TermId → List AW → Bool)
    (aw : TermId → List AW → Option Nat) (W : LState → Nat) : Prop :=
  ∀ (as : List AW) (vs : List V) (term : Term) (v : V) (st st' : LState) (c : Nat),
    γLT S iOps fOps f ctx as vs → apre term.id as = true → aw term.id as = some c →
    (sem ctx).ctor term vs st = .ok (v, st') → W st' ≤ W st + c

/-- **The oracle's runs** do not grow the measure `W`, over float-capable contexts. -/
def OracleWT (S : Clif.Inst → Bool) (iOps fOps : List Nat) (p : Program) (f : Clif.Function)
    (ctx : Ctx) (aOracle : TermId → List AW → Option AW) (W : LState → Nat) : Prop :=
  ∀ (cfg : Config), cfg.checkOverlap = false → ∀ (n : Nat) (ty : TypeId) (t : TermId)
    (as : List AW) (vs : List V) (a : AW) (s : LState) (tr : Array RuleId) (r : Option V)
    (s' : LState) (tr' : Array RuleId), aOracle t as = some a → γLT S iOps fOps f ctx as vs →
    (applyTerm p (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) → W s' ≤ W s

end Backend.Proof.Cov
