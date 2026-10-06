import FV.Backend.Proof.IselCovLe
import FV.Backend.Proof.IselFlowGen

/-!
# Form coverage of the ISLE lowering (V3): the abstract interpreter and its soundness

`aRule tab ins out r` evaluates rule `r` on abstract arguments `ins`: its patterns give a list
of abstract environments (`aPat`: a set of types is split into single types, so that a
summary sees the type its rules dispatch on; a pattern that cannot match a value gives none:
an empty value, a type or boolean constant outside the value's, an enum variant the value does
not have, a pattern the exclusion checker `fails` on), its if-lets and right-hand side are
evaluated (`aExpr`), and the result must be below `out`. Internal constructor calls go to an
oracle (`aOracle`) or to an entry of the summary table `tab` whose inputs are above the
arguments (several entries per term). Extern constructors and extractors use `actor`/`aext`
(`IselCovExt`); `apre` is the precondition of an extern constructor (an `emit`ted instruction
is covered).

`soundAt` (by induction on the interpreter's fuel): with `chkTab`, a run of a table term from
arguments its inputs describe returns a value its output describes and keeps the model's state
invariant `Is`; `root` does the same for one term whose rules each pass `aRule` or never match.
The facts about the extern helpers are the fields of `CovModel`.
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

/-! ## Transfer functions -/

/-- The value of a type constant `$n`. -/
def aprim (ty : TypeId) (n : String) : AW :=
  match primTy ty n with
  | some (.ty t) => .ty [t]
  | _ => .c0

/-- A constant pattern `$n` can match a value `a` describes. -/
def primOk (a : AW) (ty : TypeId) (n : String) : Bool :=
  match primTy ty n, a with
  | some (.ty t), .ty ts => ts.any fun u => decide (u = t)
  | _, _ => true

/-- A constant pattern `b` can match a value `a` describes. -/
def boolOk (a : AW) (b : Bool) : Bool :=
  match a with
  | .bool b' => b == b'
  | _ => true

/-- The fields of a value matched against variant `k` with `n` field patterns (`none`: it
cannot be variant `k`). -/
def aun (a : AW) (k : Nat) (n : Nat) : Option (List AW) :=
  match a with
  | .data _ k' fs => if k == k' then some fs else none
  | .alts as =>
    if as.all (fun b => match b with | .data .. => true | _ => false) then
      match as.filter (fun b => match b with | .data _ k' _ => k == k' | _ => false) with
      | [] => none
      | [.data _ _ fs] => some fs
      | bs => some (List.replicate n (.flat (AW.deepL bs).1 (AW.deepL bs).2))
    else some (List.replicate n (.flat (AW.deepL as).1 (AW.deepL as).2))
  | .flat m c => some (List.replicate n (.flat m c))
  | .xv .data => some (List.replicate n .c0)
  | _ => none

/-- The fields of a value matched against a struct pattern with `n` field patterns. -/
def aunS (a : AW) (n : Nat) : Option (List AW) :=
  match a with
  | .data _ _ fs => some fs
  | .alts as => some (List.replicate n (.flat (AW.deepL as).1 (AW.deepL as).2))
  | .flat m c => some (List.replicate n (.flat m c))
  | .xv .data => some (List.replicate n .c0)
  | _ => none

/-- The pattern cannot match a value `a` describes (beyond the shape checks). -/
def aPrune (p : Program) (a : AW) (q : Pattern) : Bool :=
  a.isBot ||
  match a with
  | .xv e => fails p e.toAV q
  | _ => false

/-- Summary table: per entry, an internal term, its abstract inputs and output. -/
abbrev Tab := List (TermId × List AW × AW)

/-- The output of an entry of `t` whose inputs are above `as`: the first with inputs equivalent
to `as`, else the first above them. -/
def tabGet (tab : Tab) (t : TermId) (as : List AW) : Option AW :=
  match tab.find? (fun e => e.1 == t && AW.leAll as e.2.1 && AW.leAll e.2.1 as) with
  | some e => some e.2.2
  | none => (tab.find? fun e => e.1 == t && AW.leAll as e.2.1).map (·.2.2)

section Eval
variable (p : Program) (tab : Tab) (aext : TermId → AW → List AW) (actor : TermId → List AW → AW)
  (apre : TermId → List AW → Bool) (aOracle : TermId → List AW → Option AW)

mutual
/-- The abstract environments after matching `q` against a value `a` describes. -/
def aPat (a : AW) (q : Pattern) (env : List AW) : List (List AW) :=
  if aPrune p a q then [] else
  match q with
  | .bind _ x sub => (AW.split a).flatMap fun b => aPat b sub (env.set x b)
  | .and _ ps => aPatAll a ps env
  | .term _ t args =>
    match termOf p t with
    | .ok term =>
      match term.kind with
      | .enumVariant k =>
        match aun a k args.length with
        | some fs => aPatArgs fs args env
        | none => []
      | .struct =>
        match aunS a args.length with
        | some fs => aPatArgs fs args env
        | none => []
      | .decl _ _ (some (.external _ _)) => aPatArgs (aext term.id a) args env
      | _ => [env]
    | .error _ => [env]
  | .constPrim ty n => if primOk a ty n then [env] else []
  | .constBool _ b => if boolOk a b then [env] else []
  | _ => [env]
/-- `aPat` of every pattern of a list, against the same value. -/
def aPatAll (a : AW) : List Pattern → List AW → List (List AW)
  | [], env => [env]
  | q :: qs, env => (aPat a q env).flatMap fun e => aPatAll a qs e
/-- Patterns against abstract values pointwise (`top` past the end). -/
def aPatArgs : List AW → List Pattern → List AW → List (List AW)
  | a :: as, q :: qs, env => (aPat a q env).flatMap fun e => aPatArgs as qs e
  | [], q :: qs, env => (aPat .top q env).flatMap fun e => aPatArgs [] qs e
  | _, [], env => [env]
end

/-- Abstract application of term `t` (result type `ty`). -/
def aApply (ty : TypeId) (t : TermId) (as : List AW) : Option AW :=
  if as.any AW.isBot then some .bot else
  match termOf p t with
  | .ok term =>
    match term.kind with
    | .enumVariant k => some (.data ty k as)
    | .struct => some (.data ty 0 as)
    | .decl _ (some (.external _)) _ =>
      if apre term.id as then some (actor term.id as) else none
    | .decl _ (some .internal) _ =>
      match aOracle t as with
      | some a => some a
      | none => tabGet tab t as
    | _ => some .top
  | .error _ => some .top

mutual
/-- Abstract value of an expression (`none`: a check failed). -/
def aExpr : Isle.Expr → List AW → Option AW
  | .var _ x, env => some (env.getD x .top)
  | .constBool _ b, _ => some (.bool b)
  | .constInt .., _ => some .c0
  | .constPrim ty n, _ => some (aprim ty n)
  | .let _ bs body, env =>
    match aBinds bs env with
    | some env' => aExpr body env'
    | none => none
  | .term ty t args, env =>
    match aArgs args env with
    | some as => aApply p tab actor apre aOracle ty t as
    | none => none
/-- Abstract values of arguments. -/
def aArgs : List Isle.Expr → List AW → Option (List AW)
  | [], _ => some []
  | e :: es, env =>
    match aExpr e env, aArgs es env with
    | some a, some as => some (a :: as)
    | _, _ => none
/-- Abstract `let*` bindings. -/
def aBinds : List (VarId × TypeId × Isle.Expr) → List AW → Option (List AW)
  | [], env => some env
  | (x, _, e) :: bs, env =>
    match aExpr e env with
    | some a => aBinds bs (env.set x a)
    | none => none
end

/-- Abstract if-lets: the environments after them (`none`: a check failed). -/
def aIfLets : List IfLet → List AW → Option (List (List AW))
  | [], env => some [env]
  | il :: ils, env =>
    match aExpr p tab actor apre aOracle il.rhs env with
    | some a =>
      ((aPat p aext a il.lhs env).mapM fun e => aIfLets ils e).map List.flatten
    | none => none

/-- The abstract environments after a rule's match phase. -/
def aRuleEnvs (ins : List AW) (r : Rule) : Option (List (List AW)) :=
  ((aPatArgs p aext ins r.args (List.replicate r.vars.length .top)).mapM
    fun e => aIfLets p tab aext actor apre aOracle r.iflets e).map List.flatten

/-- Rule `r` checks with inputs `ins` and output `out`. -/
def aRule (ins : List AW) (out : AW) (r : Rule) : Bool :=
  match aRuleEnvs p tab aext actor apre aOracle ins r with
  | some envs => envs.all fun env =>
    match aExpr p tab actor apre aOracle r.rhs env with
    | some a => AW.le a out
    | none => false
  | none => false

/-- Every rule of every table entry checks. -/
def chkTab : Bool :=
  tab.all fun e => (p.rulesOf e.1).all (aRule p tab aext actor apre aOracle e.2.1 e.2.2)

end Eval

end Backend.Proof.Cov
