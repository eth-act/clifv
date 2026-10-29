module

public import FV.Opt.Proof.RuleIntSplit

@[expose] public section

/-!
# Splitting on `isInt` on demand

`opt_split_int` splits every type variable, so a rule with several type variables of which
only one reaches `Rust.tyInt` (the amount type `kty` of `iconst_u kty k`, not the shifted type
`ty`) does its whole right-hand side once per combination. `opt_int_retry tac` runs `tac`; if it
fails, it looks for the fewest type variables whose `isInt` split lets `tac` succeed on every
case (iterative deepening over the locals `t : Clif.Ty` without an `isInt` hypothesis).
-/

namespace Opt.Proof

open Lean Meta Elab Tactic

/-- The locals `t : Clif.Ty` of the main goal without a hypothesis `t.isInt = true` or
`¬t.isInt = true`. -/
def intSplitCandidates : TacticM (List Expr) := withMainContext do
  let lctx ← getLCtx
  let mut out := []
  for d in lctx do
    if d.isImplementationDetail then continue
    unless (← instantiateMVars d.type).isConstOf ``Clif.Ty do continue
    let x := d.toExpr
    let mut has := false
    for d' in lctx do
      if d'.isImplementationDetail then continue
      let t ← instantiateMVars d'.type
      let t := if t.isAppOfArity ``Not 1 then t.appArg! else t
      if t.isAppOfArity ``Eq 3 && t.appFn!.appArg!.isAppOfArity ``Clif.Ty.isInt 1 &&
          t.appFn!.appArg!.appArg! == x then
        has := true
        break
    unless has do out := out ++ [x]
  return out

/-- `tac` on the main goal after at most `depth` nested `isInt` splits; fails if no choice of
splits lets `tac` succeed on every case. -/
partial def intAttempt (tac : Syntax) (depth : Nat) : TacticM Unit := do
  let s ← saveState
  try
    withoutRecover (evalTactic tac)
  catch e =>
    s.restore
    if depth = 0 then throw e
    for x in ← intSplitCandidates do
      let s' ← saveState
      try
        let xs ← withMainContext <| Term.exprToSyntax x
        evalTactic (← `(tactic| rcases Classical.em (Clif.Ty.isInt $xs = true) with hint | hint))
        let mut out := []
        for g in ← getGoals do
          setGoals [g]
          intAttempt tac (depth - 1)
          out := out ++ (← getGoals)
        setGoals out
        return
      catch _ =>
        s'.restore
    throw e

/-- `intAttempt` with the fewest splits (up to `fuel`). -/
def intRetry (tac : Syntax) (fuel : Nat) : TacticM Unit := do
  let s ← saveState
  for d in List.range fuel do
    try
      intAttempt tac d
      return
    catch _ =>
      s.restore
  intAttempt tac fuel

/-- `opt_int_retry tac`: `tac` on every goal, splitting type variables on `isInt` only as far as
`tac` needs. -/
elab "opt_int_retry " t:tactic : tactic => do
  let mut out := []
  for g in ← getGoals do
    setGoals [g]
    intRetry t 2
    out := out ++ (← getGoals)
  setGoals out

set_option hygiene false in
/-- `rule_auto_z` with the type variables split on `isInt` (`opt_split_int`), and
`rule_rhs_x`, whose evaluation after a `split` also uses `tyInt_ofClif_notInt`. -/
syntax "rule_auto_zi " ident : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_zi $r:ident) => `(tactic| (
      rule_intro $r
      rule_no_iflets
      rule_lhs hG
      all_goals opt_split_i128
      all_goals opt_split_int
      all_goals rule_rhs_x [tyInt_ofClif_notInt]
      all_goals (opt_some_subst; rule_finish_b)))

end Opt.Proof
