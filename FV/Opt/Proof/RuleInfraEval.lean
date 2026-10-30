import FV.Opt.Proof.InterpEval

/-!
# `opt_eval_head`: forward evaluation that only normalises the head computation

`opt_eval` (`InterpEval.lean`) alternates one `rw` with an equation lemma of the interpreter
(`opt_unfold`) and `simp` passes over the whole hypothesis (`opt_norm`). On long right-hand sides
(the magic-number `div` sequences of `RuleSkeleton3`/`RuleSkeleton5`, about 500 steps per
evaluation) both grow with the hypothesis: every `simp` pass re-traverses every pending
continuation (`fun p => …` of a `bind`, with its unreduced `match`es), and every step tries the
~50 equation lemmas with `rw`, each a full `kabstract` of the hypothesis.

`opt_eval_head` gives the same evaluation with two changes:

* `opt_bind_head`, a `simp` pre-procedure: of a `bind`, only the first computation is
  simplified; the continuation is left as it is until the first computation is a value
  (`Except.ok a >>= f` becomes `f a`, `Except.error e >>= f` becomes `Except.error e`, both by
  definition), and is then simplified as the new head.
* `opt_unfold_head`: `opt_unfold` that skips the equation lemmas whose left-hand side has a head
  symbol (with its number of arguments) that no closed subterm of the hypothesis has; `kabstract`
  could not match those. The others are tried by `rw` in `opt_unfold`'s order.

Rule modules opt in by calling `opt_eval_head`/`opt_norm_head` in their templates (the skeleton
`div` templates do).
-/

namespace Opt.Proof

open Lean Meta Simp in
/-- Of `x >>= f`, simplify only `x`; reduce `Except.ok a >>= f` to `f a` and
`Except.error e >>= f` to `Except.error e` without visiting `f`. -/
simproc_decl opt_bind_head (Bind.bind _ _) := fun e => do
  let_expr Bind.bind m inst α β x k := e | return .continue
  let r ← Simp.simp x
  let r' ← mkCongrFun (← mkCongrArg (mkAppN e.getAppFn #[m, inst, α, β]) r) k
  let m ← whnfR m
  if m.isAppOfArity ``Except 1 then
    if r.expr.isAppOfArity ``Except.ok 3 then
      return .visit (← r'.mkEqTrans { expr := (mkApp k r.expr.appArg!).headBeta })
    if r.expr.isAppOfArity ``Except.error 3 then
      let err := mkApp3 (mkConst ``Except.error m.getAppFn.constLevels!) m.appArg! β r.expr.appArg!
      return .visit (← r'.mkEqTrans { expr := err })
  return .done r'

example (f : Nat → Except String Nat) (h : (Except.ok 1 >>= f) = .ok 2) : f 1 = .ok 2 := by
  simp only [↓opt_bind_head] at h; exact h

example (f : Nat → Except String Nat) :
    (Except.error "e" >>= fun a => f a >>= f : Except String Nat) = .error "e" := by
  simp only [↓opt_bind_head]

open Lean Meta in
/-- The heads (`HeadIndex`, number of arguments) of the closed applications in `e`. -/
partial def optClosedHeads (e : Lean.Expr) :
    StateM (Std.HashSet Lean.Expr × Std.HashSet (HeadIndex × Nat)) Unit := do
  if (← get).1.contains e then return
  modify fun (v, s) => (v.insert e, s)
  if e.isApp && !e.hasLooseBVars then
    modify fun (v, s) => (v, s.insert (e.toHeadIndex, e.headNumArgs))
  match e with
  | .app f a => optClosedHeads f; optClosedHeads a
  | .lam _ d b _ | .forallE _ d b _ => optClosedHeads d; optClosedHeads b
  | .letE _ t v b _ => optClosedHeads t; optClosedHeads v; optClosedHeads b
  | .mdata _ b | .proj _ _ b => optClosedHeads b
  | _ => pure ()

open Lean Meta Elab Tactic in
/-- `opt_unfold h` without the `rw` attempts that cannot match (see the module docstring). The
lemmas and their order are `opt_unfold`'s. -/
elab "opt_unfold_head " h:ident : tactic => do
  let lems : Array Name := #[``Isle.Interp.evalExprN.eq_7, ``Isle.Interp.evalExprN.eq_2,
    ``Isle.Interp.evalExprN.eq_3, ``Isle.Interp.evalExprN.eq_4, ``Isle.Interp.evalExprN.eq_5,
    ``Isle.Interp.evalExprN.eq_6, ``Isle.Interp.evalArgsN.eq_2, ``Isle.Interp.evalArgsN.eq_3,
    ``Isle.Interp.evalBindsN.eq_2, ``Isle.Interp.evalBindsN.eq_3, ``Isle.Interp.applyTermN.eq_2,
    ``Isle.Interp.matchIfLetsN.eq_2, ``Isle.Interp.matchIfLetsN.eq_3,
    ``Isle.Interp.applyTerm.eq_2, ``Isle.Interp.selectRule.eq_3, ``Isle.Interp.selectRule.eq_2,
    ``Isle.Interp.tryRule.eq_2, ``Isle.Interp.matchRule.eq_2, ``Isle.Interp.matchIfLets.eq_2,
    ``Isle.Interp.matchIfLets.eq_3, ``Isle.Interp.evalExpr.eq_7, ``Isle.Interp.evalExpr.eq_2,
    ``Isle.Interp.evalExpr.eq_3, ``Isle.Interp.evalExpr.eq_4, ``Isle.Interp.evalExpr.eq_5,
    ``Isle.Interp.evalExpr.eq_6, ``Isle.Interp.evalArgs.eq_2, ``Isle.Interp.evalArgs.eq_3,
    ``Isle.Interp.evalBinds.eq_2, ``Isle.Interp.evalBinds.eq_3, ``Isle.Interp.matchArgs.eq_1,
    ``Isle.Interp.matchArgs.eq_2, ``Isle.Interp.matchPat.eq_1, ``Isle.Interp.matchPat.eq_2,
    ``Isle.Interp.matchPat.eq_3, ``Isle.Interp.matchPat.eq_4, ``Isle.Interp.matchPat.eq_5,
    ``Isle.Interp.matchPat.eq_6, ``Isle.Interp.matchPat.eq_7, ``Isle.Interp.matchPat.eq_8,
    ``Isle.Interp.matchPatN.eq_1, ``Isle.Interp.matchPatN.eq_2, ``Isle.Interp.matchPatN.eq_3,
    ``Isle.Interp.matchPatN.eq_4, ``Isle.Interp.matchPatN.eq_5, ``Isle.Interp.matchPatN.eq_6,
    ``Isle.Interp.matchPatN.eq_7, ``Isle.Interp.matchPatN.eq_8, ``Isle.Interp.matchArgsN.eq_1,
    ``Isle.Interp.matchArgsN.eq_2]
  let heads ← withMainContext do
    let e ← instantiateMVars (← getLocalDeclFromUserName h.getId).type
    pure ((optClosedHeads e).run ({}, {})).2.2
  for l in lems do
    let some (_, lhs, _) := (← forallTelescopeReducing (← inferType (← mkConstWithLevelParams l))
        fun _ b => pure b.eq?) | continue
    unless heads.contains (lhs.toHeadIndex, lhs.headNumArgs) do continue
    let s ← saveState
    try
      evalTactic (← `(tactic| rw [$(mkIdent l):ident] at $h:ident))
      return
    catch _ => s.restore
  throwError "opt_unfold_head: no equation lemma of the interpreter applies to {h.getId}"

/-- `opt_norm` with `opt_bind_head`. -/
syntax "opt_norm_head " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
macro_rules
  | `(tactic| opt_norm_head $h:ident) => `(tactic| opt_norm_head $h [])
  | `(tactic| opt_norm_head $h:ident [$ts,*]) => `(tactic|
      repeat (first
        | simp (disch := assumption) only [↓opt_bind_head, opt_data, $ts,*] at $h:ident
        | simp (disch := assumption) only [↓opt_bind_head, opt_monad, opt_imm, $ts,*] at $h:ident))

/-- `opt_eval` with `opt_norm_head` and `opt_unfold_head`. -/
syntax "opt_eval_head " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
macro_rules
  | `(tactic| opt_eval_head $h:ident) => `(tactic| opt_eval_head $h [])
  | `(tactic| opt_eval_head $h:ident [$ts,*]) => `(tactic|
      (opt_norm_head $h [$ts,*]; repeat (opt_unfold_head $h; opt_norm_head $h [$ts,*])))

end Opt.Proof
