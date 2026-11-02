import FV.Isle.Lookup
import FV.Backend.Proof.IselPrgDom

/-!
# Progress of the ISLE lowering (V7): the abstract interpreter

A summary table `PTab` lists, per entry, an internal term `t`, abstract inputs `ins`, an
abstract output `out`, whether the term surely returns a value (`osome`), and a fuel `fu`.
`chkTab` checks every entry against every rule of its term:

* the **match phase** of every rule (`aRule`: argument patterns `aPat`, then the if-lets
  `aIfLets`) never throws on values `ins` describes: every enum/struct pattern meets a value of
  its type with the right number of fields, every extern extractor is modeled on the value
  (`aext`; an infallible one never fails), every constant is modeled, every variable is bound;
  it yields the abstract environments of a successful match and whether it surely succeeds;
* the **right-hand side** of every rule (`aExpr`) never throws from those environments: every
  extern constructor is modeled (`actor`; a total one never fails), every internal call goes to a
  table entry whose inputs are above its arguments (`tabFind`), and its value is below `out`
  (and surely a value if `osome`);
* **exhaustiveness**: for a total term (or `osome`), every case of the inputs (`PA.splitL`) is
  surely matched by some rule (`mustRule`), so the interpreter never reports `noRule`;
* only the rules `selectRule` may try are checked (`reach`): those up to the first one that
  surely matches;
* **fuel**: `fu` covers the interpreter's fuel use (`selCost`: one unit per rule tried; costs of
  the if-lets and right-hand sides, calls costing the callee entry's `fu`), so a run from fuel
  `fu` never runs out.

`aext` (extractors), `actor` (constructors) and `aidata` (the fields of the `InstructionData` of
an E instruction, per variant) are parameters; their soundness is `IselPrgModel`'s `Model`. So is
`hand`: the rules whose right-hand side is proven by hand (`HandOk`), where the abstract
interpretation is too coarse (a relation between two matched constants).
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Isle Isle.Interp Isle.Aarch64

/-- An entry: internal term, abstract inputs, abstract output, surely a value, fuel. -/
abbrev PEnt := TermId × List PA × PA × Bool × Nat

/-- The summary table. -/
abbrev PTab := List PEnt

namespace PEnt
def t (e : PEnt) : TermId := e.1
def ins (e : PEnt) : List PA := e.2.1
def out (e : PEnt) : PA := e.2.2.1
def osome (e : PEnt) : Bool := e.2.2.2.1
def fu (e : PEnt) : Nat := e.2.2.2.2
end PEnt

/-- The value of the type constant `$n` (`sem`'s `prim`). -/
def primP (ty : TypeId) (n : String) : Option V :=
  if ty == TyId.Type then (CTy.ofName? n).map .ty else none

/-- The abstract value of an integer literal of ISLE type `ty` (`sem`'s `int`: `normInt`). -/
def aint (ty : TypeId) (i : Int) : PA := .int (some (normInt ty i)) (some (normInt ty i))

/-- The entry of `t` whose inputs are above `as`: the first with inputs equivalent to `as`, else
the first above them. -/
def tabFind (tab : PTab) (t : TermId) (as : List PA) : Option PEnt :=
  match tab.find? fun e => e.t == t && PA.leL as e.ins && PA.leL e.ins as with
  | some e => some e
  | none => tab.find? fun e => e.t == t && PA.leL as e.ins

/-- Pointwise union of two field lists of the same length. -/
def joinL : List PA → List PA → Option (List PA)
  | [], [] => some []
  | a :: as, b :: bs => (joinL as bs).map (.alts [a, b] :: ·)
  | _, _ => none

/-- The fields of a value matched against variant `k` of the enum `ty`: `none` if the value may
not be data of type `ty` (the interpreter would throw); `some (none, _)` if it is never variant
`k`; `some (some fs, must)` with the fields, `must` if it is surely variant `k`. -/
def aun (aidata : Nat → Option (List PA)) (ty : TypeId) (k : Nat) :
    PA → Option (Option (List PA) × Bool)
  | .bot => some (none, false)
  | .data t k' fs => if t == ty then (if k == k' then some (some fs, true) else some (none, false))
    else none
  | .idata => if ty == tyInstData then some (aidata k, false) else none
  | .alts as => aunAlts aidata ty k as
  | _ => none
where
  /-- `aun` of alternatives: the union of the fields of those that may be variant `k`. -/
  aunAlts (aidata : Nat → Option (List PA)) (ty : TypeId) (k : Nat) :
      List PA → Option (Option (List PA) × Bool)
    | [] => some (none, true)
    | a :: as => do
      let (x, m) ← aun aidata ty k a
      let (y, m') ← aunAlts aidata ty k as
      match x, y with
      | none, y => pure (y, false)
      | some fs, none => pure (some fs, m && m' && as.isEmpty)
      | some fs, some gs => pure ((← joinL fs gs), m && m')

/-- The fields of a value matched against a struct pattern of type `ty`. -/
def aunS (ty : TypeId) : PA → Option (List PA)
  | .data t _ fs => if t == ty then some fs else none
  | _ => none

section Eval
variable (p : Program) (tab : PTab) (aext : TermId → PA → Option (List (List PA) × Bool))
  (actor : TermId → List PA → Option (PA × Bool)) (aidata : Nat → Option (List PA))
  (hand : RuleId → Option (Nat × PA))

/-- Combine the results of matching from several environments. -/
def comb (rs : List (List AEnv × Bool)) : List AEnv × Bool :=
  (rs.flatMap (·.1), rs.all (·.2))

mutual
/-- **Abstract matching** of `q` against a value `a` describes, from environment `env`: `none`
if the match may throw; else the environments of a successful match and whether it surely
succeeds. -/
def aPat (a : PA) (q : Pattern) (env : AEnv) : Option (List AEnv × Bool) :=
  if a.isBot then some ([], false) else
  match q with
  | .bind _ x sub => if x < env.length then aPat a sub (env.set x (some a)) else none
  | .var _ x =>
    match env[x]? with
    | some (some _) => some ([env], false)
    | _ => none
  | .constBool _ b =>
    match a with
    | .bool (some c) => some (if b == c then ([env], true) else ([], false))
    | _ => some ([env], false)
  | .constInt ty i =>
    let c := normInt ty i
    match a with
    | .int lo hi =>
      if (match lo with | some l => decide (c < l) | none => false) ||
          (match hi with | some h => decide (h < c) | none => false) then some ([], false)
      else some ([env], lo == some c && hi == some c)
    | _ => some ([env], false)
  | .constPrim ty n =>
    match primP ty n with
    | none => none
    | some (.ty t) =>
      match a with
      | .ty ts => some (if ts.contains t then ([env], ts.all (· == t)) else ([], false))
      | _ => some ([env], false)
    | some _ => some ([env], false)
  | .wildcard _ => some ([env], true)
  | .and _ ps => aPatAll a ps env
  | .term ty t args =>
    match termOfT p t with
    | .error _ => none
    | .ok term =>
      match term.kind with
      | .enumVariant k =>
        match aun aidata ty k a with
        | none => none
        | some (none, _) => some ([], false)
        | some (some fs, must) =>
          (aPatArgs fs args env).map fun r => (r.1, must && r.2)
      | .struct =>
        match aunS ty a with
        | none => none
        | some fs => aPatArgs fs args env
      | .decl flags _ (some (.external _ infallible)) =>
        if flags.isMulti then none else
        match aext term.id a with
        | none => none
        | some (outs, must) =>
          if infallible && !must then none else
          (outs.mapM fun fs => aPatArgs fs args env).map fun rs =>
            let r := comb rs
            (r.1, must && r.2)
      | _ => none
/-- Every pattern of a list against the same value (`and`). -/
def aPatAll (a : PA) : List Pattern → AEnv → Option (List AEnv × Bool)
  | [], env => some ([env], true)
  | q :: qs, env => do
    let (envs, m) ← aPat a q env
    let rs ← envs.mapM fun e => aPatAll a qs e
    let r := comb rs
    pure (r.1, m && r.2)
/-- Patterns against values pointwise (the same number: else the interpreter may throw). -/
def aPatArgs : List PA → List Pattern → AEnv → Option (List AEnv × Bool)
  | [], [], env => some ([env], true)
  | a :: as, q :: qs, env => do
    let (envs, m) ← aPat a q env
    let rs ← envs.mapM fun e => aPatArgs as qs e
    let r := comb rs
    pure (r.1, m && r.2)
  | _, _, _ => none
end

/-- **Abstract application** of term `t` (result type `ty`) to arguments `as`: the result, whether
it is surely a value, and the fuel `applyTerm` needs. -/
def aApply (ty : TypeId) (t : TermId) (as : List PA) : Option (PA × Bool × Nat) :=
  if as.any PA.isBot then some (.bot, true, 1) else
  match termOfT p t with
  | .error _ => none
  | .ok term =>
    match term.kind with
    | .enumVariant k => some (.data ty k as, true, 1)
    | .struct => some (.data ty 0 as, true, 1)
    | .decl flags (some (.external _)) _ =>
      if flags.isMulti then none else
      match actor term.id as with
      | none => none
      | some (a, mustOk) => if !flags.isPartial && !mustOk then none else some (a, mustOk, 1)
    | .decl flags (some .internal) _ =>
      if flags.isMulti then none else
      (tabFind tab t as).map fun e => (e.out, e.osome, e.fu)
    | _ => none

mutual
/-- **Abstract evaluation** of an expression: its value, whether it is surely a value (no
`partial` constructor fails), and the fuel `evalExpr` needs; `none` if it may throw. -/
def aExpr : Isle.Expr → AEnv → Option (PA × Bool × Nat)
  | .var _ x, env =>
    match env[x]? with
    | some (some a) => some (a, true, 1)
    | _ => none
  | .constBool _ b, _ => some (.bool (some b), true, 1)
  | .constInt ty i, _ => some (aint ty i, true, 1)
  | .constPrim ty n, _ =>
    match primP ty n with
    | some (.ty t) => some (.ty [t], true, 1)
    | _ => none
  | .let _ bs body, env => do
    let (env', m1, c1) ← aBinds bs env
    let (a, m2, c2) ← aExpr body env'
    pure (a, m1 && m2, 1 + max c1 c2)
  | .term ty t args, env => do
    let (as, m1, c1) ← aArgs args env
    let (a, m2, c2) ← aApply p tab actor ty t as
    pure (a, m1 && m2, 1 + max c1 c2)
/-- Abstract evaluation of arguments (left to right). -/
def aArgs : List Isle.Expr → AEnv → Option (List PA × Bool × Nat)
  | [], _ => some ([], true, 1)
  | e :: es, env => do
    let (a, m1, c1) ← aExpr e env
    let (as, m2, c2) ← aArgs es env
    pure (a :: as, m1 && m2, 1 + max c1 c2)
/-- Abstract `let*` bindings. -/
def aBinds : List (VarId × TypeId × Isle.Expr) → AEnv → Option (AEnv × Bool × Nat)
  | [], env => some (env, true, 1)
  | (x, _, e) :: bs, env => do
    let (a, m1, c1) ← aExpr e env
    if x < env.length then
      let (env', m2, c2) ← aBinds bs (env.set x (some a))
      pure (env', m1 && m2, 1 + max c1 c2)
    else none
end

/-- The largest cost of a list of results. -/
def maxCost (cs : List Nat) : Nat := cs.foldl max 1

/-- **Abstract if-lets**: the environments after them, whether they surely succeed, and the fuel
`matchIfLets` needs. -/
def aIfLets : List IfLet → AEnv → Option (List AEnv × Bool × Nat)
  | [], env => some ([env], true, 1)
  | il :: ils, env => do
    let (a, m1, c1) ← aExpr p tab actor il.rhs env
    let (envs, m2) ← aPat p aext aidata a il.lhs env
    let rs ← envs.mapM fun e => aIfLets ils e
    pure (rs.flatMap (·.1), m1 && m2 && rs.all (·.2.1), 1 + max c1 (maxCost (rs.map (·.2.2))))

/-- **The match phase of a rule** on abstract arguments: the environments of a successful match,
whether it surely succeeds, and the fuel of its if-lets. -/
def aRule (ins : List PA) (r : Rule) : Option (List AEnv × Bool × Nat) := do
  let (envs, m) ← aPatArgs p aext aidata ins r.args (List.replicate r.vars.length none)
  let rs ← envs.mapM fun e => aIfLets p tab aext actor aidata r.iflets e
  pure (rs.flatMap (·.1), m && rs.all (·.2.1), maxCost (rs.map (·.2.2)))

/-- Rule `r` surely matches the arguments `ins` describes. -/
def mustRule (ins : List PA) (r : Rule) : Bool :=
  match aRule p tab aext actor aidata ins r with
  | some (_, m, _) => m
  | none => false

/-- Every case of the arguments is surely matched by some rule. -/
def exhaustive (rules : List Rule) (ins : List PA) : Bool :=
  rules.any (mustRule p tab aext actor aidata ins) ||
    (PA.splitL ins).all fun s => rules.any (mustRule p tab aext actor aidata s)

/-- The rules `selectRule` may try on arguments `ins` describes: up to the first that surely
matches. -/
def reach (ins : List PA) : List Rule → List Rule
  | [] => []
  | r :: rs => if mustRule p tab aext actor aidata ins r then [r] else r :: reach ins rs

/-- One rule of an entry: its match never throws, and its right-hand side never throws from any
environment of a successful match, with a value below `out` (surely a value if `osome`). The fuel
of its if-lets and of its right-hand side. A **hand-checked** rule (`hand r.id = some (c, a)`,
its right-hand side proven by hand to return a value `a` describes from fuel `c`:
`IselPrgModel`'s `HandOk`) needs only `a` below `out` when it may match. -/
def ruleCost (ins : List PA) (out : PA) (osome : Bool) (r : Rule) : Option (Nat × Nat) := do
  let (envs, _, ilc) ← aRule p tab aext actor aidata ins r
  match hand r.id with
  | some (c, a) => if envs.isEmpty || PA.le a out then pure (ilc, c) else none
  | none =>
    let rcs ← envs.mapM fun env => do
      let (a, m, c) ← aExpr p tab actor r.rhs env
      if PA.le a out && (!osome || m) then pure c else none
    pure (ilc, maxCost rcs)

/-- The fuel `selectRule` needs to try every rule (`tryRule` costs two units above the
if-lets). -/
def selCost : List (Nat × Nat) → Nat
  | [] => 1
  | (ilc, _) :: cs => 1 + max (2 + ilc) (selCost cs)

/-- **The check of one entry.** -/
def chkEntry (e : PEnt) : Bool :=
  match termOf p e.t with
  | .error _ => false
  | .ok term =>
    match term.kind with
    | .decl flags (some .internal) _ =>
      !flags.isMulti &&
      let rules := reach p tab aext actor aidata e.ins (p.rulesOf e.t)
      match rules.mapM (ruleCost p tab aext actor aidata hand e.ins e.out e.osome) with
      | some cs =>
        decide (1 + max (selCost cs) (maxCost (cs.map (·.2))) ≤ e.fu) &&
        ((flags.isPartial && !e.osome) || exhaustive p tab aext actor aidata rules e.ins)
      | none => false
    | _ => false

/-- **Every entry checks.** -/
def chkTab : Bool := tab.all (chkEntry p tab aext actor aidata hand)

end Eval

end Backend.Proof.Prg
