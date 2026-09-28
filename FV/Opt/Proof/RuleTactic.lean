import Lean

/-!
# Tactics for the rule proofs

`opt_destruct`: split every hypothesis that is an `∃`, `∧` or `∨` (the last into several
goals), repeatedly, then `subst` every variable equation. Used after unfolding a rule's
left-hand side relation (`ArgsRel`), whose existentials must become context variables before
later equations (e.g. `d = .data …` for an `InstructionData` bound earlier) can be
substituted.
-/

namespace Opt.Proof

open Lean Meta Elab Tactic

/-- One `cases` on the first `∃`/`∧`/`∨`/`False` hypothesis, if any. -/
def destructStep (g : MVarId) : MetaM (Option (List MVarId)) := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← whnfR (← instantiateMVars d.type)
    if t.isAppOfArity ``Exists 2 || t.isAppOfArity ``And 2 || t.isAppOfArity ``Or 2 ||
        t.isConstOf ``False then
      let subgoals ← g.cases d.fvarId
      return some (subgoals.toList.map (·.mvarId))
  return none

/-- Destructure until no `∃`/`∧`/`∨` hypothesis is left (at most `fuel` steps per goal). -/
partial def destructAll (fuel : Nat) (g : MVarId) : MetaM (List MVarId) := do
  if fuel = 0 then return [g]
  match ← destructStep g with
  | none => return [g]
  | some gs => return (← gs.mapM (destructAll (fuel - 1))).flatten

elab "opt_destruct" : tactic => do
  let gs ← getGoals
  let mut out : List MVarId := []
  for g in gs do
    out := out ++ (← destructAll 1000 g)
  setGoals out

end Opt.Proof

namespace Opt.Proof
open Lean Meta Elab Tactic

/-- Marker: the model facts of a hypothesis whose type has hash `h` were added (`opt_model`;
a number, so that `simp_all` leaves it alone). -/
def OptSeen (_h : Nat) : Prop := True

/-- For every hypothesis `h` such that `f hG h` typechecks (`f` one of the given lemma names),
add `f hG h` unless `h`'s type is marked `OptSeen`; then mark it. -/
def addModelFacts (hG : Expr) (lemmas : List Name) : TacticM Bool := withMainContext do
  let mut added := false
  let lctx ← getLCtx
  let mut seen : Array Nat := #[]
  for d in lctx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``OptSeen 1 then
      if let some k := t.appArg!.rawNatLit? then seen := seen.push k
      else if let some k := (t.appArg!.nat?) then seen := seen.push k
  for d in lctx do
    if d.isImplementationDetail then continue
    let dty ← instantiateMVars d.type
    let key := dty.hash.toNat
    if seen.contains key then continue
    for lem in lemmas do
      let pf? ← observing? (mkAppM lem #[hG, d.toExpr])
      if let some pf := pf? then
        let ty ← instantiateMVars (← inferType pf)
        seen := seen.push key
        let g ← getMainGoal
        let (_, g) ← (← g.assert (← mkFreshUserName `hsem) ty pf).intro1P
        let mark := mkApp (mkConst ``OptSeen) (mkNatLit key)
        let (_, g) ← (← g.assert (← mkFreshUserName `hseen) mark (mkConst ``True.intro)).intro1P
        replaceMainGoal [g]
        added := true
        break
  return added

/-- `opt_model hG`: add the graph model's facts (`GraphOk.node_sem`, `GraphOk.type_sem`) for
every node-membership and class-type hypothesis. Fails if nothing new was added. -/
elab "opt_model " hG:term : tactic => withMainContext do
  let hGe ← elabTerm hG none
  let added ← addModelFacts hGe [`Opt.Proof.GraphOk.node_sem, `Opt.Proof.GraphOk.type_sem]
  unless added do throwError "opt_model: nothing to add"

end Opt.Proof

namespace Opt.Proof
open Lean Meta Elab Tactic

/-- `opt_rw_lhs`: for a goal `l = r`, rewrite `l` with a hypothesis `h : l = c` (syntactically
the same left-hand side). -/
elab "opt_rw_lhs" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (_, l, _) := t.eq? | throwError "opt_rw_lhs: goal is not an equation"
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let dt ← instantiateMVars d.type
    if let some (_, l', _) := dt.eq? then
      if l' == l then
        let r ← g.rewrite t d.toExpr
        let g' ← g.replaceTargetEq r.eNew r.eqProof
        replaceMainGoal (g' :: r.mvarIds)
        return
  throwError "opt_rw_lhs: no hypothesis for {l}"

end Opt.Proof

namespace Opt.Proof
open Lean Meta Elab Tactic

/-- `opt_cases_ty`: `cases` every local variable of type `Clif.Ty`. -/
elab "opt_cases_ty" : tactic => do
  let rec go (g : MVarId) (fuel : Nat) : MetaM (List MVarId) := g.withContext do
    if fuel = 0 then return [g]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if (← instantiateMVars d.type).isConstOf `Clif.Ty then
        let gs ← g.cases d.fvarId
        return (← gs.toList.mapM fun s => go s.mvarId (fuel - 1)).flatten
    return [g]
  let gs ← getGoals
  let mut out := []
  for g in gs do out := out ++ (← go g 8)
  setGoals out

end Opt.Proof
