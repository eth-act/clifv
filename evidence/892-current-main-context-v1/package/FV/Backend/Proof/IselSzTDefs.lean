import FV.Isle.Lookup
import FV.Backend.Proof.IselSzDefs
import FV.Backend.Proof.IselCovTFam
import FV.Backend.Proof.IselCovTCheck

/-!
# The size of the ISLE lowering's output over float-capable contexts (typed V6c): the cost analysis

`IselSzDefs`' cost analysis on the typed abstract interpreter (`Backend.Proof.CovT`, `AT`): the
extern costs `actorW`/`actorT` (an `emit`'s weight `emitW`/targets `emitT` of the instruction
values an `AT` describes), the cost table `CTab` and the evaluation `cApply`/`cExpr`/`cArgs`/
`cBinds`/`cIfLets`/`cRule`/`chkCost` over `aExpr`/`aPat`/`aRuleEnvs` (`IselCovTCheck`), and the
facts the soundness assumes, `ExtW`/`OracleW` (with the typed meaning `γL`). The weights
(`szInstW`, `wtA`, `tgA`, `emitK`, `loadConstW`, `retsW`, `varT`), the hand-rule fact `HandW` and
the driver's contract (`IselSz`, `stmtSzB`, `termSzB`, …) are `IselSzDefs`', which do not depend
on the abstract domain.
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64
open Backend.Proof.Cov (emitK loadConstW retsW varT)

/-! ## Extern costs -/

/-- The weight of an `emit`ted instruction value `a` describes: `emitK` if every variant it may
have is neither `Call`, `CallInd` nor `JTSequence`. -/
def emitW (a : AT) : Option Nat :=
  let okK (k : Nat) : Bool :=
    k != VIdx.MInst.Call && k != VIdx.MInst.CallInd && k != VIdx.MInst.JTSequence
  match a with
  | .data t k _ => if t == tyMInst && okK k then some emitK else none
  | .alts as =>
    if as.all (fun b => match b with
      | .data t k _ => t == tyMInst && okK k
      | _ => false) then some emitK else none
  | _ => none

/-- The branch targets of an `emit`ted instruction value `a` describes: the maximum over the
variants it may have (none for a `JTSequence`). -/
def emitT (a : AT) : Option Nat :=
  match a with
  | .data t k _ => if t == tyMInst then varT k else none
  | .alts as =>
    (as.mapM fun (b : AT) => match b with
      | .data t k _ => if t == tyMInst then varT k else none
      | _ => none).map fun (ns : List Nat) => ns.foldl max 0
  | _ => none

/-- **Extern constructors**: the branch targets they emit (only `emit`'s instruction has any). -/
def actorT (id : TermId) (as : List AT) : Option Nat :=
  if id == TId.emit then
    match as with
    | [a] => emitT a
    | _ => none
  else some 0

/-- **Extern constructors**: the weight they emit (`none`: not bounded here). -/
def actorW (id : TermId) (as : List AT) : Option Nat :=
  if id == TId.emit then
    match as with
    | [a] => emitW a
    | _ => none
  else if id == TId.load_constant_full then some loadConstW
  else if id == TId.gen_return then some retsW
  else if id == TId.gen_call_args then none
  else some 0

/-! ## The cost analysis -/

/-- Cost table: per entry, an internal term, its abstract inputs and a weight. -/
abbrev CTab := List (TermId × List AT × Nat)

/-- The weight of an entry of `t` whose inputs are above `as`. -/
def ctabGet (ctab : CTab) (t : TermId) (as : List AT) : Option Nat :=
  (ctab.find? fun e => e.1 == t && AT.leAllF as e.2.1).map (·.2.2)

section Eval
variable (p : Program) (tab : Tab) (aw : TermId → List AT → Option Nat) (ctab : CTab)
  (aext : TermId → AT → List AT)
  (actor : TermId → List AT → AT) (apre : TermId → List AT → Bool)
  (aOracle : TermId → List AT → Option AT)

/-- The weight an application of term `t` to values `as` describes emits (mirrors `aApply`:
`some` only where `aApply` is). -/
def cApply (_ty : TypeId) (t : TermId) (as : List AT) : Option Nat :=
  if as.any AT.isBot then some 0 else
  match termOfT p t with
  | .ok term =>
    match term.kind with
    | .enumVariant _ => some 0
    | .struct => some 0
    | .decl _ (some (.external _)) _ =>
      if apre term.id as then aw term.id as else none
    | .decl _ (some .internal) _ =>
      match aOracle t as with
      | some _ => some 0
      | none =>
        match tabGet tab t as with
        | some _ => ctabGet ctab t as
        | none => none
    | _ => some 0
  | .error _ => some 0

mutual
/-- The weight evaluating an expression emits (`none`: not bounded, or `aExpr` fails). -/
def cExpr : Isle.Expr → List AT → Option Nat
  | .var .., _ => some 0
  | .constBool .., _ => some 0
  | .constInt .., _ => some 0
  | .constPrim .., _ => some 0
  | .let _ bs body, env =>
    match aBinds p tab actor apre aOracle bs env, cBinds bs env with
    | some env', some c =>
      match cExpr body env' with
      | some d => some (c + d)
      | none => none
    | _, _ => none
  | .term ty t args, env =>
    match aArgs p tab actor apre aOracle args env, cArgs args env with
    | some as, some c =>
      match cApply p tab aw ctab apre aOracle ty t as with
      | some d => some (c + d)
      | none => none
    | _, _ => none
/-- The weight evaluating arguments emits. -/
def cArgs : List Isle.Expr → List AT → Option Nat
  | [], _ => some 0
  | e :: es, env =>
    match cExpr e env, cArgs es env with
    | some c, some d => some (c + d)
    | _, _ => none
/-- The weight evaluating `let*` bindings emits. -/
def cBinds : List (VarId × TypeId × Isle.Expr) → List AT → Option Nat
  | [], _ => some 0
  | (x, _, e) :: bs, env =>
    match aExpr p tab actor apre aOracle e env, cExpr e env with
    | some a, some c =>
      match cBinds bs (env.set x a) with
      | some d => some (c + d)
      | none => none
    | _, _ => none
end

/-- The weight the if-lets emit, on every path of abstract environments (the maximum). -/
def cIfLets : List IfLet → List AT → Option Nat
  | [], _ => some 0
  | il :: ils, env =>
    match aExpr p tab actor apre aOracle il.rhs env, cExpr p tab aw ctab actor apre aOracle il.rhs env with
    | some a, some c =>
      match (aPat p aext a il.lhs env).mapM fun e => cIfLets ils e with
      | some ds => some (c + ds.foldl max 0)
      | none => none
    | _, _ => none

/-- The weight a run of rule `r` on values `ins` describes emits: its if-lets (on every
environment of its argument patterns) and its right-hand side (on every environment after its
if-lets). -/
def cRule (ins : List AT) (r : Rule) : Option Nat :=
  match (aPatArgs p aext ins r.args (List.replicate r.vars.length .top)).mapM
      (cIfLets p tab aw ctab aext actor apre aOracle r.iflets),
    aRuleEnvs p tab aext actor apre aOracle ins r with
  | some cs, some envs =>
    match envs.mapM (cExpr p tab aw ctab actor apre aOracle r.rhs) with
    | some ds => some (cs.foldl max 0 + ds.foldl max 0)
    | none => none
  | _, _ => none

/-- Rule `r` on values `ins` emits at most weight `c`. -/
def cRuleLe (ins : List AT) (c : Nat) (r : Rule) : Bool :=
  match cRule p tab aw ctab aext actor apre aOracle ins r with
  | some c' => decide (c' ≤ c)
  | none => false

/-- Every rule of every entry of the cost table emits at most the entry's weight. -/
def chkCost : Bool :=
  ctab.all fun e => (p.rulesOf e.1).all (cRuleLe p tab aw ctab aext actor apre aOracle e.2.1 e.2.2)

end Eval

/-! ## The facts the soundness of the cost analysis assumes -/

section Facts

/-- **Extern constructors** emit at most their cost: `aw` bounds the growth of the measure `W`
of the lowering state for arguments the abstract values describe. -/
def ExtW (f : Clif.Function) (ctx : Ctx) (apre : TermId → List AT → Bool)
    (aw : TermId → List AT → Option Nat) (W : LState → Nat) : Prop :=
  ∀ (as : List AT) (vs : List V) (term : Term) (v : V) (st st' : LState) (c : Nat),
    γL f ctx as vs → apre term.id as = true → aw term.id as = some c →
    (sem ctx).ctor term vs st = .ok (v, st') → W st' ≤ W st + c

/-- **The oracle's runs** do not grow the measure `W`. -/
def OracleW (p : Program) (f : Clif.Function) (ctx : Ctx) (aOracle : TermId → List AT → Option AT)
    (W : LState → Nat) : Prop :=
  ∀ (cfg : Config), cfg.checkOverlap = false → ∀ (n : Nat) (ty : TypeId) (t : TermId)
    (as : List AT) (vs : List V) (a : AT) (s : LState) (tr : Array RuleId) (r : Option V)
    (s' : LState) (tr' : Array RuleId), aOracle t as = some a → γL f ctx as vs →
    (applyTerm p (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) → W s' ≤ W s


end Facts

end Backend.Proof.CovT
