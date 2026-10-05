import Lean
import FV.Backend.Isel

/-!
# Splitting the big matchers of the extern helpers without equation lemmas

`externCtor`, `externExtract` and `MInst.ofV` dispatch with one `match` on a term id (or variant
index) and argument shapes: ~100 overlapping alternatives with a fall-through default. Lean's
`split` (and `simp [externCtor]`) build the matcher's splitter/equation lemmas, whose
"previous alternatives did not match" hypotheses make that infeasible.

`gen_match_split thm matcher` instead proves, once, a splitter without those hypotheses:

    ∀ (β : Type) (P : discrs → β → Prop) discrs alts,
      (∀ xs, P pats₁ (alt₁ xs)) → … → (∀ xs, P patsₙ (altₙ xs)) →
        P discrs (matcher (fun _ … => β) discrs alts)

by unfolding the matcher's compiled decision tree (a chain of `dite (x = k)` on the dispatch
literal, then `_sparseCasesOn` case splits on the arguments): `dite_step` splits one `dite`,
`sparse_step` cases the free variable a `_sparseCasesOn` application scrutinises and contracts
the applications whose scrutinee became a constructor (one iota step, through the recursor, so
the kernel only sees reductions over free variables); every leaf is an alternative applied to
arguments, closed by its hypothesis. A property of `externCtor` then reduces to one goal per
alternative (`apply`, then beta).
-/

namespace Backend.Proof.FlowSplit

open Lean Meta Elab Tactic Command

/-- A `_sparseCasesOn` auxiliary of the match compiler. -/
def isSparse (n : Name) : Bool := (n.toString.splitOn "_sparseCasesOn").length > 1

/-- A case-splitting head: a `_sparseCasesOn` auxiliary, a recursor or a `casesOn`. -/
def isSplitHead (env : Environment) (n : Name) : Bool :=
  isSparse n || isCasesOnRecursor env n ||
    match env.find? n with
    | some (.recInfo _) => true
    | _ => false

/-- The scrutinee of a case-splitting application: a recursor's major premise, otherwise the
first explicit argument (`_sparseCasesOn`) or the argument after motive and indices
(`casesOn`). -/
def sparseMajor (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let args := e.getAppArgs
  let env ← getEnv
  if let .const n _ := e.getAppFn then
    if let some (.recInfo rv) := env.find? n then
      return args[rv.getMajorIdx]?
    if isCasesOnRecursor env n then
      let some (.inductInfo iv) := env.find? n.getPrefix | return none
      return args[iv.numParams + 1 + iv.numIndices]?
  let info ← getFunInfo e.getAppFn
  for i in [0:args.size] do
    if h : i < info.paramInfo.size then
      if info.paramInfo[i].isExplicit then return some args[i]!
  return none

/-- The case-splitting applications of `e`, outermost first. -/
partial def collectSparse (env : Environment) (e : Lean.Expr) : Array Lean.Expr :=
  let here := match e.getAppFn with
    | .const n _ => if isSplitHead env n then #[e] else #[]
    | _ => #[]
  let sub := match e with
    | .app f a => collectSparse env f ++ collectSparse env a
    | .lam _ t b _ => collectSparse env t ++ collectSparse env b
    | .forallE _ t b _ => collectSparse env t ++ collectSparse env b
    | .letE _ t v b _ => collectSparse env t ++ collectSparse env v ++ collectSparse env b
    | .mdata _ b => collectSparse env b
    | .proj _ _ b => collectSparse env b
    | _ => #[]
  here ++ sub

/-- Contract every `_sparseCasesOn` application whose scrutinee is a constructor application:
unfold the auxiliary, one recursor (iota) step, beta. -/
def reduceSparse (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    if let .const n _ := e.getAppFn then
      let env ← getEnv
      if isSplitHead env n then
        if let some m ← sparseMajor e then
          let isCtor := match m.getAppFn with
            | .const c _ => env.isConstructor c
            | _ => false
          if isCtor then
            let isRec := match env.find? n with
              | some (.recInfo _) => true
              | _ => false
            let e1 ← if isRec then pure (some e) else unfoldDefinition? e
            if let some e1 := e1 then
              if let some e2 ← Meta.reduceRecMatcher? e1.headBeta then
                return .visit (← Core.betaReduce e2)
    return .done e)

/-- Case on the variable a `_sparseCasesOn` application scrutinises. -/
def sparseStep (g : MVarId) : MetaM (Option (List MVarId)) := do
  let t ← instantiateMVars (← g.getType)
  let found ← g.withContext do
    let mut res : Option FVarId := none
    for e in collectSparse (← getEnv) t do
      if let some m ← sparseMajor e then
        if m.isFVar then
          res := some m.fvarId!
          break
    pure res
  match found with
  | none => pure none
  | some fv =>
    let gs ← g.cases fv
    let mut out := []
    for sg in gs do
      let ty ← instantiateMVars (← sg.mvarId.getType)
      let ty' ← sg.mvarId.withContext (reduceSparse ty)
      out := out ++ [← sg.mvarId.replaceTargetDefEq ty']
    pure (some out)

/-- Split the outermost closed `dite` of the goal. -/
def diteStep (g : MVarId) : TacticM (Option (List MVarId)) := do
  let t ← instantiateMVars (← g.getType)
  match t.find? (fun e => e.isAppOfArity ``dite 5 && !(e.getArg! 1).hasLooseBVars) with
  | none => pure none
  | some e =>
    let cs ← g.withContext (Term.exprToSyntax (e.getArg! 1))
    setGoals [g]
    evalTactic (← `(tactic| by_cases hd : $cs))
    let gs ← getGoals
    setGoals [gs[0]!]
    evalTactic (← `(tactic| rw [dite_eq_left_of_eq_true (eq_true hd)]))
    evalTactic (← `(tactic| try subst hd))
    evalTactic (← `(tactic| try dsimp only [Eq.ndrec_symm]))
    let gp ← getGoals
    setGoals [gs[1]!]
    evalTactic (← `(tactic| rw [dite_eq_right_of_eq_false (eq_false hd)]))
    let gn ← getGoals
    pure (some (gp ++ gn))

/-- Close a leaf `P pats (a xs)` with the hypothesis `∀ xs, P pats (a xs)` of the alternative
`a`. -/
def closeLeaf (hyps : Array (FVarId × Lean.Expr)) (g : MVarId) : MetaM Bool := do
  let t ← instantiateMVars (← g.getType)
  let t ← Core.betaReduce t
  let arg := t.appArg!
  let fn := arg.getAppFn
  if !fn.isFVar then return false
  match hyps.find? (·.1 == fn.fvarId!) with
  | none => return false
  | some (_, h) =>
    let pf := mkAppN h arg.getAppArgs
    if ← isDefEq (← inferType pf) t then
      g.assign pf
      return true
    else return false

/-- `gen_match_split thm matcher`: prove the splitter (module doc) of `matcher` as `thm`. -/
elab "gen_match_split " thm:ident mat:ident : command => liftTermElabM do
  let matName ← realizeGlobalConstNoOverload mat
  let info ← getConstInfo matName
  let some minfo ← getMatcherInfo? matName | throwError "{matName} is not a matcher"
  let lvls := info.levelParams.map fun _ => Level.one
  let ty := info.type.instantiateLevelParams info.levelParams lvls
  let .forallE _ motTy _ _ := ty | throwError "unexpected matcher type"
  withLocalDeclD `β (.sort Level.one) fun β => do
  let pTy ← forallTelescope motTy fun xs _ => do mkForallFVars xs (← mkArrow β (.sort Level.zero))
  withLocalDeclD `P pTy fun P => do
  let motive ← forallTelescope motTy fun xs _ => mkLambdaFVars xs β
  let ty2 ← instantiateForall ty #[motive]
  forallTelescope ty2 fun ys _ => do
    let discrs := ys.extract 0 minfo.numDiscrs
    let alts := ys.extract minfo.numDiscrs ys.size
    let mut hypTys : Array (Name × Lean.Expr) := #[]
    let mut i := 0
    for a in alts do
      let aty ← inferType a
      let hty ← forallTelescope aty fun zs body => do
        mkForallFVars zs (mkApp (mkAppN P body.getAppArgs) (mkAppN a zs))
      hypTys := hypTys.push (.mkSimple s!"H{i}", hty)
      i := i + 1
    withLocalDeclsDND hypTys fun hs => do
      let goal := mkApp (mkAppN P discrs) (mkAppN (mkConst matName lvls) (#[motive] ++ ys))
      let mvar ← mkFreshExprMVar goal
      let hyps := (alts.zip hs).map fun (a, h) => (a.fvarId!, h)
      -- unfold the matcher, then walk its decision tree
      let g0 := mvar.mvarId!
      let g1 ← g0.withContext do
        let some val := info.value? | throwError "cannot unfold {matName}"
        let val := val.instantiateLevelParams info.levelParams lvls
        let body := val.beta (#[motive] ++ ys)
        g0.replaceTargetDefEq (mkApp (mkAppN P discrs) body)
      let _ ← Tactic.run g1 (do
        let mut todo := [g1]
        let mut unsolved := #[]
        while !todo.isEmpty do
          let g := todo.head!
          todo := todo.tail
          if ← g.isAssigned then continue
          match ← diteStep g with
          | some gs => todo := gs ++ todo
          | none =>
            match ← sparseStep g with
            | some gs => todo := gs ++ todo
            | none =>
              unless ← g.withContext (closeLeaf hyps g) do unsolved := unsolved.push g
        unless unsolved.isEmpty do
          throwError "gen_match_split: {unsolved.size} unsolved leaves, first:\n{unsolved[0]!}"
        setGoals [])
      let pf ← instantiateMVars mvar
      let stmt ← mkForallFVars (#[β, P] ++ ys ++ hs) goal
      let pf ← mkLambdaFVars (#[β, P] ++ ys ++ hs) pf
      addDecl (.thmDecl { name := thm.getId, levelParams := [], type := stmt, value := pf })

end Backend.Proof.FlowSplit
