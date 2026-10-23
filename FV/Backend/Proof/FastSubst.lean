import Lean

/-!
# `subst_vars` without default-transparency `whnf` of the equation sides

`Lean.Meta.substVars` substitutes one variable per scan of the local context and restarts. On
each scan, `subst` puts both sides of every equation hypothesis into `whnf` at default
transparency to look for a variable. In the isel inversion proofs the context holds many
equations between large interpreter terms (`externCtor ctx …`, `Interp.applyTerm …`), so every
rescan unfolds them again: `subst_vars` took about 95% of `IselCtlTry`.

`substVars` below looks for a variable side after `instantiateMVars` and, failing that, after
`whnfR` (reducible unfolding and projections of constructors, e.g. `(a, b).1 = x`). It never
unfolds non-reducible definitions. Every module importing this one (through `IselCmpBase`, the
isel tactic hub) runs it for every `subst_vars`, also the ones inside the isel macros
(numbers in LEARNINGS.md).
-/

namespace Backend.Proof.FastSubst

open Lean Meta

/-- `e` as a free variable: syntactically, else its `whnfR`. -/
def sideFVar? (e : Expr) : MetaM (Option Expr) := do
  let e ← instantiateMVars e
  if e.isFVar then return some e
  let e' ← whnfR e
  return if e'.isFVar then some e' else none

/-- One substitution (`rhs` a variable first, else `lhs`), or `none`. -/
def substSomeVar? (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    match ← matchEq? ldecl.type with
    | some (_, lhs, rhs) =>
      let r? ← sideFVar? rhs
      let l? ← if r?.isSome then pure none else sideFVar? lhs
      if r?.isNone && l?.isNone then continue
      let ty ← mkEq (l?.getD (← instantiateMVars lhs)) (r?.getD (← instantiateMVars rhs))
      let res ← observing? do
        let g1 ← if ty == ldecl.type then pure g else g.replaceLocalDeclDefEq ldecl.fvarId ty
        substCore g1 ldecl.fvarId (symm := r?.isSome) (tryToSkip := true)
      if let some (_, g') := res then return some g'
    | none =>
      if (← matchHEq? ldecl.type).isSome then
        if let some g' ← subst? g ldecl.fvarId then return some g'
  return none

/-- Substitute until no equation has a variable side. -/
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
