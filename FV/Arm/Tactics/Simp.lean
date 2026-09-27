/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
-- Modified by fv-compiler-rust (2026): ported to Lean v4.34.1, module prefix FV.Arm, wrapped in namespace Arm.
import Lean
import FV.Arm.Attr
import FV.Arm.Tactics.Attr

namespace Arm

open Lean Elab Tactic Expr Meta

open Meta.DiscrTree in
/-- `fixSimpTheoremKey` will regenerate the key of a simp theorem with
`noIndexAtArgs` set to `false`.

For context: `mkSimpTheorems` sets `noIndexAtArgs := true`, meaning that all
a rewrite like `h_x0_s10 : r (.GPR 0#5) s10 = 42` will have `[r, *, *]` as key
in the discrimination tree.
This causes many unneeded, and expensive, attempts at unification.

`fixSimpTheoremKey` fixes up those keys, so that the `h_x0_s10` example will get
a key that includes the state and statefield constant

FIXME: we should suggest a PR upstream that adds `noIndexAtArgs` as
an optional argument to `mkSimpTheorems`, so that we can control
this properly -/
def fixSimpTheoremKey (thm : SimpTheorem) : MetaM SimpTheorem := do
  let type ← inferType thm.proof
  let ⟨_, _, type⟩ ← forallMetaTelescope type
  match type.eq? with
    | none =>
        trace[Tactic.sym] "{Lean.crossEmoji} {type} is not an equality\
          , giving up on fixing the discrtree keys.

          Currently, the keys are:\n{thm.keys}"
        pure thm
    | some (_eqType, lhs, _rhs) =>
        let keys ← mkPath lhs (noIndexAtArgs := false)
        pure { thm with keys }

/-- Build the `SimpTheorem`s for a local proof `e` (analogous to what `simp [e]` does),
with the given origin. -/
def mkSimpTheoremsOfExpr (origin : Origin) (e : Expr) (prio : Nat := eval_prio default) :
    MetaM (Array SimpTheorem) :=
  mkSimpTheoremFromExpr origin #[] e (prio := prio)

/-- Add an array of simp theorems to a `SimpTheorems` set. -/
def addSimpTheoremEntries (s : SimpTheorems) (thms : Array SimpTheorem) : SimpTheorems :=
  thms.foldl SimpTheorems.addSimpTheorem s

/- Create a context for using the `simp` tactic during symbolic
simulation in LNSym proofs. -/
def LNSymSimpContext
  (config : Simp.Config := {decide := true})
  (simp_attrs : Array Name := #[`minimal_theory, `bitvec_rules, `state_simp_rules])
  -- Functions to unfold during simp.
  (decls_to_unfold : Array Name := #[])
  -- Theorems to use during simp.
  (thms : Array Name := #[])
  -- Local hypotheses to use during simp.
  (decls : Array LocalDecl := #[])
  -- Other expressions to use during simp
  (exprs : Array Expr := #[])
  -- Simprocs to add to the default set.
  (simprocs : Array Name := #[])
  -- Whether the default simprocs should be used.
  (useDefaultSimprocs : Bool := true)
  -- argument to `DiscrTree.mkPath`
  (noIndexAtArgs : Bool := true)
  : MetaM (Simp.Context × Array Simp.Simprocs) := do
  let mut ext_simpTheorems := #[]
  let mut all_simprocs : Array Simp.Simprocs := #[]
  if useDefaultSimprocs then
    all_simprocs := all_simprocs.push (← Simp.getSimprocs)

  for a in simp_attrs do
    let some ext ← (getSimpExtension? a) |
                   throwError m!"[LNSymSimpContext] Error: {a} simp attribute not found!"
    ext_simpTheorems := #[(← ext.getTheorems)] ++ ext_simpTheorems

    if let some ext ← (Simp.getSimprocExtension? a) then
      let s ← ext.getSimprocs
      all_simprocs := all_simprocs.push s
  let mut const_simpTheorems := ({} : SimpTheorems)
  for d in decls_to_unfold do
    const_simpTheorems ← const_simpTheorems.addDeclToUnfold d
  for t in thms do
    const_simpTheorems ← const_simpTheorems.addConst t

  let exprs := exprs ++ (decls.map fun d => Expr.fvar d.fvarId)
  for e in exprs do
    let origin :=
      if let Expr.fvar id := e then
        .fvar id
      else
        .other (← mkFreshUserName `sym_n)
    let mut newThms ← mkSimpTheoremsOfExpr origin e
    if noIndexAtArgs = false then
      newThms ← newThms.mapM fixSimpTheoremKey
    const_simpTheorems := addSimpTheoremEntries const_simpTheorems newThms

  let all_simpTheorems := (#[const_simpTheorems] ++ ext_simpTheorems)
  let ctx ← Simp.mkContext (config := config)
    (simpTheorems := all_simpTheorems)
    (congrTheorems := (← Meta.getSimpCongrTheorems))
  for s in simprocs do
    all_simprocs ← Simp.SimprocsArray.add all_simprocs s false
  return (ctx, all_simprocs)

/- Invoke the `simp` tactic during symbolic simulation in LNSym
proofs. -/
def LNSymSimp (goal : MVarId)
   (ctx : Simp.Context) (simprocs : Array Simp.Simprocs)
  -- Provide an FVarID (i.e., a hypothesis) to simplify; when none is provided,
  -- the goal is simplified.
   (fvarid : Option FVarId := none) : MetaM (Option MVarId) := goal.withContext do
  match fvarid with
  | none =>
    let (new_goal, _) ← simpGoal goal ctx simprocs
                        (simplifyTarget := true) (discharge? := none)
    match new_goal with
    | none => return none
    | some (_, goal') => return goal'
  | some fid =>
    let (new_goal, _) ← simpLocalDecl goal fid ctx simprocs
    match new_goal with
    | none => return none
    | some (_, goal') => return goal'

/--
Invoke `simp [..] at *` at the given goal `g` with
simp context `ctx` and simprocs `simprocs`.
-/
def LNSymSimpAtStar (g : MVarId)
    (ctx : Simp.Context)
    (simprocs : Array Simp.Simprocs)
    : MetaM (Option MVarId) := do
   g.withContext do
    let fvars : Array FVarId :=
      (← getLCtx).foldl (init := #[]) fun fvars d => fvars.push d.fvarId
    let (result, _stats) ← simpGoal g ctx simprocs (fvarIdsToSimp := fvars)
      (simplifyTarget := true) (discharge? := none)
    match result with
    | none => return none
    | some (_newHyps, g') => pure g'

end Arm
