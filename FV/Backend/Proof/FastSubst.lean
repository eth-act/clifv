import Lean

/-!
# `subst_vars` without `whnf` of the equation sides

`Lean.Meta.substVars` substitutes one variable per scan of the local context and restarts. On
each scan, `subst` puts both sides of every equation hypothesis into `whnf` at default
transparency to look for a variable. In the isel inversion proofs the context holds many
equations between large interpreter terms (`externCtor ctx …`, `Interp.applyTerm …`), so every
rescan reduces them again: `subst_vars` took about 95% of `IselCtlTry` and `IselTermFactsCall`.

`fastSubstVars` makes the same substitutions in the same order (a variable's first equation,
`rhs` before `lhs`, `substCore` with `tryToSkip`), but reads the sides syntactically (after
`instantiateMVars`, as `substVar` already does for variables). It differs from `subst_vars`
only on an equation whose side is not a variable but reduces to one.

Every module importing this one (through `IselCmpBase`, the isel tactic hub) runs it for every
`subst_vars`, also the ones inside the isel macros: `IselCtlTry` 806 → 101 s, `KillTryDefs`
1,802 → 70 s (LEARNINGS.md).
-/

namespace Backend.Proof.FastSubst

open Lean Meta

/-- One step of `Lean.Meta.substVars` (`substSomeVar?`) without `whnf` of equation sides.
`none` when nothing is substituted. -/
def substSomeVar? (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let lctx ← getLCtx
  for ldecl in lctx do
    if ldecl.isImplementationDetail then continue
    match ← matchEq? ldecl.type with
    | some (_, lhs, rhs) =>
      -- `subst` on an equation: `rhs` is a variable, else `lhs` is one
      let lhs ← instantiateMVars lhs
      let rhs ← instantiateMVars rhs
      let r? ←
        if rhs.isFVar then observing? (substCore g ldecl.fvarId (symm := true) (tryToSkip := true))
        else if lhs.isFVar then observing? (substCore g ldecl.fvarId (symm := false) (tryToSkip := true))
        else pure none
      if let some (_, g') := r? then return some g'
    | none =>
      if (← matchHEq? ldecl.type).isSome then
        if let some g' ← subst? g ldecl.fvarId then return some g'
        continue
      if ldecl.isLet then continue
      -- `subst` on a variable `x` (`substVar`): its first equation `t = x` or `x = t`
      let x := ldecl.fvarId
      let found ← lctx.findDeclM? fun d => do
        if d.isImplementationDetail then return none
        match ← matchEq? d.type with
        | some (_, lhs, rhs) =>
          let lhs ← instantiateMVars lhs
          let rhs ← instantiateMVars rhs
          if rhs.isFVar && rhs.fvarId! == x then
            if !(← exprDependsOn lhs x) then return some (d.fvarId, true)
          if lhs.isFVar && lhs.fvarId! == x then
            if !(← exprDependsOn rhs x) then return some (d.fvarId, false)
          return none
        | none => return none
      if let some (h, symm) := found then
        if let some (_, g') ← observing? (substCore g h (symm := symm) (tryToSkip := true)) then
          return some g'
  return none

/-- `Lean.Meta.substVars` without `whnf` of equation sides. -/
partial def substVars (g : MVarId) : MetaM MVarId := do
  match ← substSomeVar? g with
  | some g' => substVars g'
  | none => return g

open Elab Tactic in
/-- `subst_vars` without `whnf` of equation sides (`Backend.Proof.FastSubst.substVars`). -/
elab "fast_subst_vars" : tactic => do
  replaceMainGoal [← substVars (← getMainGoal)]

/-- Every `subst_vars` runs `fast_subst_vars`. -/
macro_rules | `(tactic| subst_vars) => `(tactic| fast_subst_vars)

end Backend.Proof.FastSubst
