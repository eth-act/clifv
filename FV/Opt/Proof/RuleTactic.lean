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

/-- One `cases` on the first `∃`/`∧`/`∨`/`False` hypothesis, or on an equation between two
`Clif.Val` constructors (dependent unification: `⟨t, b⟩ = ⟨t', b'⟩` substitutes the type and
the bits where they are variables; `simp`'s `Val.mk.injEq` would leave a `HEq` that `simp_all`
loses), if any. -/
def destructStep (g : MVarId) : MetaM (Option (List MVarId)) := g.withContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← whnfR (← instantiateMVars d.type)
    if t.isAppOfArity ``Exists 2 || t.isAppOfArity ``And 2 || t.isAppOfArity ``Or 2 ||
        t.isConstOf ``False then
      let subgoals ← g.cases d.fvarId
      return some (subgoals.toList.map (·.mvarId))
    if let some (ty, l, r) := t.eq? then
      if ty.isConstOf `Clif.Val && l.isAppOfArity `Clif.Val.mk 2 && r.isAppOfArity `Clif.Val.mk 2 then
        if let some subgoals ← observing? (g.cases d.fvarId) then
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

/-- Marker: the model facts of a pair of hypotheses with key `h` were added (`opt_model`;
a number, so that `simp_all` leaves it alone). -/
def OptSeen (_h : Nat) : Prop := True

/-- The `(state, class)` of a class-value term `den st x` (a local applied to two arguments). -/
def denKey? (e : Expr) : Option (Expr × Expr) :=
  if e.getAppFn.isFVar && e.getAppNumArgs == 2 then some (e.getArg! 0, e.getArg! 1) else none

/-- For every hypothesis `h₂ : den st x = some c` and every hypothesis `h₁` about the same
`(st, x)` — a node `i ∈ G.enodes st x` (`GraphOk.node_val`) or a type
`G.typeOf st x = some t` (`GraphOk.type_val`) — add `lemma hG h₁ h₂` unless the pair (`h₁`'s
type, the left-hand side of `h₂`) is marked `OptSeen`; then mark it. Pairs are matched on the
syntax of `(st, x)` first, so only well-typed applications are elaborated. -/
def addPairFacts (hG : Expr) : TacticM Bool := withMainContext do
  let mut added := false
  let lctx ← getLCtx
  let mut seen : Array Nat := #[]
  let mut dens : Array (Expr × Expr × LocalDecl × Expr) := #[]
  let mut facts : Array (Name × Expr × Expr × LocalDecl × Expr) := #[]
  for d in lctx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``OptSeen 1 then
      if let some k := t.appArg!.rawNatLit? then seen := seen.push k
      else if let some k := (t.appArg!.nat?) then seen := seen.push k
    else if let some (_, l, _) := t.eq? then
      if l.isAppOfArity `Isle.Opt.EGraph.typeOf 4 then
        facts := facts.push (`Opt.Proof.GraphOk.type_val, l.getArg! 2, l.getArg! 3, d, t)
      else if let some (st, x) := denKey? l then
        dens := dens.push (st, x, d, l)
    else if t.isAppOfArity ``Membership.mem 5 then
      let c := t.getArg! 3
      if c.isAppOfArity `Isle.Opt.EGraph.enodes 4 then
        facts := facts.push (`Opt.Proof.GraphOk.node_val, c.getArg! 2, c.getArg! 3, d, t)
  for (lem, st, x, d1, t1) in facts do
    for (st', x', d2, l2) in dens do
      unless st == st' && x == x' do continue
      let key := (mixHash t1.hash l2.hash).toNat
      if seen.contains key then continue
      let pf? ← observing? (mkAppM lem #[hG, d1.toExpr, d2.toExpr])
      if let some pf := pf? then
        let ty ← instantiateMVars (← inferType pf)
        seen := seen.push key
        let g ← getMainGoal
        let (_, g) ← (← g.assert (← mkFreshUserName `hsem) ty pf).intro1P
        let mark := mkApp (mkConst ``OptSeen) (mkNatLit key)
        let (_, g) ← (← g.assert (← mkFreshUserName `hseen) mark (mkConst ``True.intro)).intro1P
        replaceMainGoal [g]
        added := true
  return added

/-- `opt_model hG`: add the graph model's facts for every node of a class whose value is a
hypothesis `den s x = some c` (`GraphOk.node_val`: the node evaluates to `c`) and for every
class type (`GraphOk.type_val`: `c.ty` is the class type). Fails if nothing new was added.
(Pairs, not `∀ c, den s x = some c → …` facts: `simp_all` loses the latter once the class value
becomes known.) -/
elab "opt_model " hG:term : tactic => withMainContext do
  let hGe ← elabTerm hG none
  let added ← addPairFacts hGe
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

/-- `opt_cases_ty`: `cases` every local variable of type `Clif.Ty` or `Clif.IntCC`. -/
elab "opt_cases_ty" : tactic => do
  let rec go (g : MVarId) (fuel : Nat) : MetaM (List MVarId) := g.withContext do
    if fuel = 0 then return [g]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if ty.isConstOf `Clif.Ty || ty.isConstOf `Clif.IntCC then
        let gs ← g.cases d.fvarId
        return (← gs.toList.mapM fun s => go s.mvarId (fuel - 1)).flatten
    return [g]
  let gs ← getGoals
  let mut out := []
  for g in gs do out := out ++ (← go g 10)
  setGoals out

end Opt.Proof

namespace Opt.Proof
open Lean Meta Elab Tactic

/-- `opt_widths`: give every local `x : BitVec e` whose width `e` reduces to a numeral (after
`cases` on a `Clif.Ty`, `e` is `Ty.width .i32` etc.) the type `BitVec n`, so that `bv_decide`
accepts it as an atom. -/
elab "opt_widths" : tactic => do
  let gs ← getGoals
  let mut out := []
  for g in gs do
    let mut g := g
    for d in (← g.getDecl).lctx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if ty.isAppOfArity ``BitVec 1 then
        let e := ty.appArg!
        if e.nat?.isSome || e.rawNatLit?.isSome then continue
        let e' ← g.withContext <| whnf e
        let some k := e'.rawNatLit? <|> e'.nat? | continue
        g ← g.replaceLocalDeclDefEq d.fvarId (mkApp (mkConst ``BitVec) (mkNatLit k))
    out := out ++ [g]
  setGoals out

end Opt.Proof

namespace Opt.Proof
open Lean Meta Elab Tactic

/-- `opt_guard tac`: run `tac`, turning a runtime exception (maximum recursion depth,
heartbeats) into an ordinary tactic failure, so that `first`/`try` can recover. -/
elab "opt_guard " t:tactic : tactic => do
  let s ← saveState
  tryCatchRuntimeEx (evalTactic t) fun e => do
    s.restore
    throwError "opt_guard: {e.toMessageData}"

end Opt.Proof
