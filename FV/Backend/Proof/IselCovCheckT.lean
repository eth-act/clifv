import FV.Backend.Proof.IselCovCheck
import FV.Backend.Proof.IselCovLeT
import FV.Backend.Proof.IselExclT

/-!
# Form coverage over float-capable contexts: the pattern checker

The typed counterpart of `IselCovCheck`'s pattern machinery: `aPruneT` prunes with the typed
checker `failsTG` (`IselExclT`, sound at a scope `S` with `CtxInvT`/`InstSplit`), and `aPatT`/
`aPatAllT`/`aPatArgsT`/`aIfLetsT`/`aRuleEnvsT`/`aRuleT`/`chkTabT` are the abstract pattern
matching, the rule check and the table check over them. The abstract application (`aApply`)
and the expression evaluation (`aExpr`/`aArgs`/`aBinds`) do not use the pattern checker and are
`IselCovCheck`'s.
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Aarch64

section Eval
variable (p : Program) (tab : Tab) (aext : TermId → AW → List AW) (actor : TermId → List AW → AW)
  (apre : TermId → List AW → Bool) (aOracle : TermId → List AW → Option AW)
  (iOps fOps : List Nat) (S : Clif.Inst → Bool)

/-- The pattern cannot match a value `a` describes (beyond the shape checks), at the scope `S`
(the typed checker `failsTG`). -/
def aPruneT (p : Program) (iOps fOps : List Nat) (a : AW) (q : Pattern) : Bool :=
  a.isBot ||
  match a with
  | .xv e => failsTG p iOps fOps (e.toAVT iOps fOps) q
  | _ => false

mutual
/-- The abstract environments after matching `q` against a value `a` describes. -/
def aPatT (a : AW) (q : Pattern) (env : List AW) : List (List AW) :=
  if aPruneT p iOps fOps a q then [] else
  match q with
  | .bind _ x sub => (AW.split a).flatMap fun b => aPatT b sub (env.set x b)
  | .and _ ps => aPatAllT a ps env
  | .term _ t args =>
    match termOf p t with
    | .ok term =>
      match term.kind with
      | .enumVariant k =>
        match aun a k args.length with
        | some fs => aPatArgsT fs args env
        | none => []
      | .struct =>
        match aunS a args.length with
        | some fs => aPatArgsT fs args env
        | none => []
      | .decl _ _ (some (.external _ _)) => aPatArgsT (aext term.id a) args env
      | _ => [env]
    | .error _ => [env]
  | .constPrim ty n => if primOk a ty n then [env] else []
  | .constBool _ b => if boolOk a b then [env] else []
  | _ => [env]
/-- `aPatT` of every pattern of a list, against the same value. -/
def aPatAllT (a : AW) : List Pattern → List AW → List (List AW)
  | [], env => [env]
  | q :: qs, env => (aPatT a q env).flatMap fun e => aPatAllT a qs e
/-- Patterns against abstract values pointwise (`top` past the end). -/
def aPatArgsT : List AW → List Pattern → List AW → List (List AW)
  | a :: as, q :: qs, env => (aPatT a q env).flatMap fun e => aPatArgsT as qs e
  | [], q :: qs, env => (aPatT .top q env).flatMap fun e => aPatArgsT [] qs e
  | _, [], env => [env]
end

/-- Abstract if-lets: the environments after them (`none`: a check failed). -/
def aIfLetsT : List IfLet → List AW → Option (List (List AW))
  | [], env => some [env]
  | il :: ils, env =>
    match aExpr p tab actor apre aOracle il.rhs env with
    | some a =>
      ((aPatT p aext iOps fOps a il.lhs env).mapM fun e => aIfLetsT ils e).map List.flatten
    | none => none

/-- The abstract environments after a rule's match phase. -/
def aRuleEnvsT (ins : List AW) (r : Rule) : Option (List (List AW)) :=
  ((aPatArgsT p aext iOps fOps ins r.args (List.replicate r.vars.length .top)).mapM
    fun e => aIfLetsT p tab aext actor apre aOracle iOps fOps r.iflets e).map List.flatten

/-- Rule `r` checks with inputs `ins` and output `out`. -/
def aRuleT (ins : List AW) (out : AW) (r : Rule) : Bool :=
  match aRuleEnvsT p tab aext actor apre aOracle iOps fOps ins r with
  | some envs => envs.all fun env =>
    match aExpr p tab actor apre aOracle r.rhs env with
    | some a => AW.le a out
    | none => false
  | none => false

/-- Every rule of every table entry checks. -/
def chkTabT : Bool :=
  tab.all fun e => (p.rulesOf e.1).all (aRuleT p tab aext actor apre aOracle iOps fOps e.2.1 e.2.2)

end Eval

end Backend.Proof.Cov
