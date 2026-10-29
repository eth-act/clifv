module

public import Lean

@[expose] public meta section

/-!
# `subst_vars` without default-transparency `whnf` of the equation sides

`Lean.Meta.substVars` substitutes one variable per scan of the local context and restarts. On
each scan, `subst` puts both sides of every equation hypothesis into `whnf` at default
transparency to look for a variable. In the isel inversion proofs the context holds many
equations between large interpreter terms (`externCtor ctx …`, `Interp.applyTerm …`), so every
rescan unfolds them again: `subst_vars` took about 95% of `IselCtlTry`.

`substVars` below is `Lean.Meta.substVars` (same scan order, same choices, same hypothesis
handling) with one change: `substEq` puts the equation sides into `whnfR` (reducible unfolding,
projections of constructors such as `(a, b).1 = x`) instead of `whnf`. It never unfolds
non-reducible definitions. Every module importing this one (through `IselCmpBase`, the isel
tactic hub) runs it for every `subst_vars`, also the ones inside the isel macros (numbers in
LEARNINGS.md).
-/

namespace Backend.Proof.FastSubst

open Lean Meta

/-- `Lean.Meta.substEq` with `whnfR` instead of `whnf` of the sides. -/
def substEq (mvarId : MVarId) (hFVarId : FVarId) : MetaM MVarId := do
  let (hFVarId, mvarId) ← heqToEq mvarId hFVarId
  mvarId.withContext do
    let localDecl ← hFVarId.getDecl
    let error {α} _ : MetaM α := throwTacticEx `subst mvarId
      m!"invalid equality proof, it is not of the form (x = t) or (t = x){indentExpr localDecl.type}"
    let some (_, lhs, rhs) ← matchEq? localDecl.type | error ()
    let substReduced (newType : Expr) (symm : Bool) : MetaM MVarId := do
      let mvarId ← mvarId.assert localDecl.userName newType (mkFVar hFVarId)
      let (hFVarId', mvarId) ← mvarId.intro1P
      let mvarId ← mvarId.clear hFVarId
      return (← substCore mvarId hFVarId' (symm := symm) (tryToSkip := true)).2
    let rhs' ← whnfR rhs
    if rhs'.isFVar then
      if rhs != rhs' then substReduced (← mkEq lhs rhs') true
      else return (← substCore mvarId hFVarId (symm := true) (tryToSkip := true)).2
    else
      let lhs' ← whnfR lhs
      if lhs'.isFVar then
        if lhs != lhs' then substReduced (← mkEq lhs' rhs) false
        else return (← substCore mvarId hFVarId (symm := false) (tryToSkip := true)).2
      else error ()

/-- `Lean.Meta.subst` with `substEq` above. -/
partial def subst (mvarId : MVarId) (h : FVarId) : MetaM MVarId :=
  mvarId.withContext do
    let type ← h.getType
    match (← matchEq? type) with
    | some _ => substEq mvarId h
    | none => match (← matchHEq? type) with
      | some _ =>
        let (h', mvarId') ← heqToEq mvarId h
        if mvarId == mvarId' then substVar mvarId h else subst mvarId' h'
      | none => substVar mvarId h

/-- One substitution, as `Lean.Meta.substSomeVar?`. -/
def substSomeVar? (mvarId : MVarId) : MetaM (Option MVarId) := mvarId.withContext do
  for localDecl in (← getLCtx) do
    if let some mvarId ← observing? (subst mvarId localDecl.fvarId) then
      return some mvarId
  return none

/-- `Lean.Meta.substVars` with `substEq` above. -/
partial def substVars (g : MVarId) : MetaM MVarId := do
  match ← substSomeVar? g with
  | some g' => substVars g'
  | none => return g

open Elab Tactic in
/-- `subst_vars` without default-transparency `whnf` (`Backend.Proof.FastSubst.substVars`). -/
elab "fast_subst_vars" : tactic => do
  replaceMainGoal [← substVars (← getMainGoal)]

/-- Every `subst_vars` runs `fast_subst_vars`. -/
macro_rules | `(tactic| subst_vars) => `(tactic| fast_subst_vars)

end Backend.Proof.FastSubst
