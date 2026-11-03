import FV.Opt.Proof.RuleEmbed
import FV.Opt.Proof.RuleCtor

/-!
# Forward evaluation of rule right-hand sides

`opt_eval at h` evaluates the interpreter call in a hypothesis
`h : (evalExprN p (sem G) cfg n e env).run s = .ok r` (or `matchIfLetsN`) on the concrete
expression of a rule: the interpreter's equation lemmas (fuel `n` of the form `k + 1000`),
the monad laws below (`opt_monad`), the data facts (`opt_data`) and the extern constructors
(`ctor_*`). The result is an equation between the computed outcome and `.ok r`.
-/

namespace Opt.Proof

open Isle Isle.Opt Isle.Interp Clif

section Monad
variable {σ α β ε : Type}

@[opt_monad] theorem except_ok_bind' (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f : Except ε β) = f a := rfl
@[opt_monad] theorem except_pure' (a : α) : (pure a : Except ε α) = .ok a := rfl
@[opt_monad] theorem except_error_bind' (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f : Except ε β) = .error e := rfl
@[opt_monad] theorem except_bind_ok (a : α) (f : α → Except ε β) :
    (Except.ok a : Except ε α).bind f = f a := rfl
@[opt_monad] theorem run_liftM'' (e : Except Err α) (s : σ × Array RuleId) :
    (liftM e : M σ α).run s = (e >>= fun a => Except.ok (a, s)) := by
  cases e <;> rfl
@[opt_monad] theorem run_pure'' (a : α) (s : σ × Array RuleId) :
    (pure a : M σ α).run s = .ok (a, s) := rfl
@[opt_monad] theorem run_bind'' (x : M σ α) (f : α → M σ β) (s : σ × Array RuleId) :
    (x >>= f).run s = (x.run s >>= fun p => (f p.1).run p.2) := rfl
@[opt_monad] theorem run_get'' (s : σ × Array RuleId) :
    (get : M σ (σ × Array RuleId)).run s = .ok (s, s) := rfl
@[opt_monad] theorem run_set'' (s s' : σ × Array RuleId) :
    (set s' : M σ PUnit).run s = .ok (⟨⟩, s') := rfl
@[opt_monad] theorem run_throw'' (e : Err) (s : σ × Array RuleId) :
    (throw e : M σ α).run s = .error e := rfl
@[opt_monad] theorem run_fire' (r : RuleId) (st : σ) (tr : Array RuleId) :
    (fire r : M σ Unit).run (st, tr) = Except.ok ((), (st, tr.push r)) := rfl
@[opt_monad] theorem run_bindAll_nil (f : α → M σ (List β)) (s : σ × Array RuleId) :
    (bindAll f []).run s = .ok ([], s) := rfl
@[opt_monad] theorem run_bindAll_cons (f : α → M σ (List β)) (a : α) (as : List α)
    (s : σ × Array RuleId) :
    (bindAll f (a :: as)).run s = ((f a).run s >>= fun p =>
      (bindAll f as).run p.2 >>= fun q => Except.ok (p.1 ++ q.1, q.2)) := rfl

end Monad

attribute [opt_monad] Bool.false_eq_true ite_true ite_false dite_true dite_false
  List.length_cons List.length_nil Nat.zero_add Nat.reduceAdd Array.size_replicate
  Array.set!_eq_setIfInBounds beq_self_eq_true Nat.lt_irrefl decide_true decide_false
  Option.some.injEq reduceIte reduceDIte bne_self_eq_false Bool.not_false Bool.not_true
  Bool.and_true Bool.true_and Bool.and_false Bool.false_and Nat.reduceLT Nat.reduceLeDiff
  Array.size_setIfInBounds Array.getElem?_setIfInBounds Array.getElem?_replicate
  Nat.reduceEqDiff List.nil_append List.cons_append List.singleton_append List.append_nil
  Option.toList_some Option.toList_none List.map_cons List.map_nil TermFlags.isMulti
  TermFlags.isPartial Term.externCtor? Term.externExtractor? Nat.lt_add_one Nat.zero_lt_succ

/-! ## Extern constructors -/

section
variable {σ : Type} (G : EGraph σ)

@[opt_monad] theorem sem_ctor' (t : Term) (args : List V) (s : St σ) :
    (sem G).ctor t args s = match t.externCtor? with
      | some fn => toExt (ctorFn G fn args s)
      | none => .unmodeled s!"{t.name} has no extern constructor" := rfl

@[opt_monad] theorem sem_toSem_ctor (t : Term) (args : List V) (s : St σ) :
    (sem G).toSem.ctor t args s = (sem G).ctor t args s := rfl

@[opt_monad] theorem sem_toSem_mkData (ty k : Nat) (fs : List V) :
    (sem G).toSem.mkData ty k fs = .data ty k fs := rfl

@[opt_monad] theorem sem_toSem_int (ty : TypeId) (i : Int) :
    (sem G).toSem.int ty i = .int (normInt ty i) := rfl

@[opt_monad] theorem toExt_ok_some' {α : Type} (a : α) : toExt (.ok (some a) : R (Option α)) = .ok a := rfl
@[opt_monad] theorem toExt_ok_none {α : Type} : toExt (.ok none : R (Option α)) = .fail := rfl
@[opt_monad] theorem toExt_error {α : Type} (e : String) : toExt (.error e : R (Option α)) = .unmodeled e := rfl

@[opt_monad] theorem ctorFn_make_inst (t : CTy) (d : V) (s : St σ) :
    ctorFn G "make_inst_ctor" [.ty t, d] s = .ok (some (makeInst G s t d)) := rfl

@[opt_monad] theorem ctorFn_subsume (x : Nat) (s : St σ) :
    ctorFn G "subsume" [.value x] s = .ok (some (.value x, { s with subsumed := x :: s.subsumed })) :=
  rfl

@[opt_monad] theorem ctorFn_remat (x : Nat) (s : St σ) :
    ctorFn G "remat" [.value x] s = .ok (some (.value x, { s with remat := x :: s.remat })) := rfl

/-- Every other extern constructor keeps the state (`ctorPure`). -/
theorem ctorFn_pure {fn : String} (h1 : fn ≠ "make_inst_ctor") (h2 : fn ≠ "remat")
    (h3 : fn ≠ "subsume") (args : List V) (s : St σ) :
    ctorFn G fn args s = ((ctorPure G fn args s).bind fun o => .ok (o.map (·, s))) := by
  unfold ctorFn
  split
  · exact absurd rfl h1
  · exact absurd rfl h2
  · exact absurd rfl h3
  · rfl

end

end Opt.Proof

namespace Opt.Proof

open Lean Elab Tactic in
/-- The equation lemmas `opt_unfold` tries, in order. -/
def optUnfoldEqns : Array Name := #[
  ``Isle.Interp.evalExprN.eq_7, ``Isle.Interp.evalExprN.eq_2, ``Isle.Interp.evalExprN.eq_3,
  ``Isle.Interp.evalExprN.eq_4, ``Isle.Interp.evalExprN.eq_5, ``Isle.Interp.evalExprN.eq_6,
  ``Isle.Interp.evalArgsN.eq_2, ``Isle.Interp.evalArgsN.eq_3, ``Isle.Interp.evalBindsN.eq_2,
  ``Isle.Interp.evalBindsN.eq_3, ``Isle.Interp.applyTermN.eq_2, ``Isle.Interp.matchIfLetsN.eq_2,
  ``Isle.Interp.matchIfLetsN.eq_3, ``Isle.Interp.applyTerm.eq_2, ``Isle.Interp.selectRule.eq_3,
  ``Isle.Interp.selectRule.eq_2, ``Isle.Interp.tryRule.eq_2, ``Isle.Interp.matchRule.eq_2,
  ``Isle.Interp.matchIfLets.eq_2, ``Isle.Interp.matchIfLets.eq_3, ``Isle.Interp.evalExpr.eq_7,
  ``Isle.Interp.evalExpr.eq_2, ``Isle.Interp.evalExpr.eq_3, ``Isle.Interp.evalExpr.eq_4,
  ``Isle.Interp.evalExpr.eq_5, ``Isle.Interp.evalExpr.eq_6, ``Isle.Interp.evalArgs.eq_2,
  ``Isle.Interp.evalArgs.eq_3, ``Isle.Interp.evalBinds.eq_2, ``Isle.Interp.evalBinds.eq_3,
  ``Isle.Interp.matchArgs.eq_1, ``Isle.Interp.matchArgs.eq_2, ``Isle.Interp.matchPat.eq_1,
  ``Isle.Interp.matchPat.eq_2, ``Isle.Interp.matchPat.eq_3, ``Isle.Interp.matchPat.eq_4,
  ``Isle.Interp.matchPat.eq_5, ``Isle.Interp.matchPat.eq_6, ``Isle.Interp.matchPat.eq_7,
  ``Isle.Interp.matchPat.eq_8, ``Isle.Interp.matchPatN.eq_1, ``Isle.Interp.matchPatN.eq_2,
  ``Isle.Interp.matchPatN.eq_3, ``Isle.Interp.matchPatN.eq_4, ``Isle.Interp.matchPatN.eq_5,
  ``Isle.Interp.matchPatN.eq_6, ``Isle.Interp.matchPatN.eq_7, ``Isle.Interp.matchPatN.eq_8,
  ``Isle.Interp.matchArgsN.eq_1, ``Isle.Interp.matchArgsN.eq_2]

open Lean Meta in
/-- The closed applications of `e` in the order `kabstract` (`rw`) visits them (pre-order, left to
right), except inside the alternatives of `match`es: `opt_norm` leaves those alternatives alone
(`opt_match_head`), so they are evaluated once a `split` has selected one. -/
partial def optVisible (e : Expr) : StateT (Std.HashSet Expr × Array Expr) MetaM Unit := do
  if (← get).1.contains e then return
  modify fun (v, a) => (v.insert e, a)
  match e with
  | .app .. =>
    if !e.hasLooseBVars then modify fun (v, a) => (v, a.push e)
    let f := e.getAppFn
    let args := e.getAppArgs
    let mut alts : Nat × Nat := (0, 0)
    if let .const n _ := f then
      if let some info ← getMatcherInfo? n then
        if args.size ≥ info.arity then
          let i := info.numParams + 1 + info.numDiscrs
          alts := (i, i + info.numAlts)
    optVisible f
    for h : i in [:args.size] do
      unless alts.1 ≤ i && i < alts.2 do optVisible args[i]
  | .lam _ d b _ | .forallE _ d b _ => optVisible d; optVisible b
  | .letE _ t v b _ => optVisible t; optVisible v; optVisible b
  | .mdata _ b | .proj _ _ b => optVisible b
  | _ => pure ()

open Lean Meta Elab Tactic in
/-- One step of `opt_eval at h`: unfold an interpreter call of `h` by the first equation lemma of
`optUnfoldEqns` that rewrites one, at the first such call in `rw`'s order outside the
alternatives of `match`es (`optVisible`). Only the lemmas of functions that occur in `h` are
tried. -/
elab "opt_unfold " h:ident : tactic => withMainContext do
  let e ← instantiateMVars (← (← getFVarId h).getType)
  let used := e.getUsedConstants
  let (_, _, cands) ← (optVisible e).run ({}, #[])
  for l in optUnfoldEqns do
    unless used.contains l.getPrefix do continue
    let s ← saveState
    try
      let pf ← mkConstWithFreshMVarLevels l
      let (xs, _, ty) ← forallMetaTelescopeReducing (← inferType pf)
      let some (_, lhs, _) := ty.eq? | continue
      let key := (lhs.toHeadIndex, lhs.headNumArgs)
      for t in cands do
        unless (t.toHeadIndex, t.headNumArgs) == key do continue
        if ← withTransparency .instances (isDefEq lhs t) then
          let eq ← instantiateMVars (mkAppN pf xs)
          if eq.hasMVar then continue
          let eqStx ← Term.exprToSyntax eq
          evalTactic (← `(tactic| rw [$eqStx:term] at $h:ident))
          return
      s.restore
    catch _ => s.restore
  throwError "opt_unfold: no equation lemma rewrites {h}"

open Lean Meta Simp in
/-- Of a `match` whose discriminants, once simplified, select no alternative, keep the
alternatives as they are (`opt_norm`): the hypothesis of a rule's right-hand side holds the
interpreter's pending `match`es (the remaining rules of a term, their pattern matches and if-lets),
and simplifying their alternatives on every step re-traversed all of them (`RuleShiftsRotate`,
`RuleExtends2`: most of the module). A `match` that reduces is reduced and simplified further. -/
simproc_decl opt_match_head (_) := fun e => do
  let .const declName _ := e.getAppFn | return .continue
  let some info ← getMatcherInfo? declName | return .continue
  if e.getAppNumArgs < info.arity then return .continue
  if let some e' ← withSimpMetaConfig <| reduceRecMatcher? e then
    return .visit { expr := e' }
  let r ← (simpMatchDiscrs? info e) <&> (·.getD { expr := e })
  if let some e' ← withSimpMetaConfig <| reduceRecMatcher? r.expr then
    return .visit (← r.mkEqTrans { expr := e' })
  match ← simpMatchCore declName r.expr with
  | .visit r' => return .visit (← r.mkEqTrans r')
  | _ => return .done r

example (x : Nat) (h : (match x + 0 with | 0 => 0 + 1 | k + 1 => k + 0) = 2) :
    (match x with | 0 => 0 + 1 | k + 1 => k + 0) = 2 := by
  simp only [↓opt_match_head, Nat.add_zero] at h; exact h

example (h : (match some 1 with | some a => a + 0 | none => 0) = 1) : True := by
  simp only [↓opt_match_head, Nat.add_zero] at h; trivial

/-- Normalise between steps: data/constructor facts and monad laws, in one `simp` call. Alternating
one call per set until neither applies traversed the whole hypothesis again on every call: up to
a third more heartbeats in `RuleExtends2` and `RuleSkeleton5`. The alternatives of a `match` that
does not reduce are left alone (`opt_match_head`). -/
syntax "opt_norm " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
macro_rules
  | `(tactic| opt_norm $h:ident) => `(tactic| opt_norm $h [])
  | `(tactic| opt_norm $h:ident [$ts,*]) => `(tactic|
      try simp (disch := assumption) only [↓opt_match_head, opt_data, opt_monad, opt_imm, $ts,*]
        at $h:ident)

/-- Evaluate the interpreter call in hypothesis `h`: alternate `opt_unfold` and `opt_norm`. -/
syntax "opt_eval " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
macro_rules
  | `(tactic| opt_eval $h:ident) => `(tactic| opt_eval $h [])
  | `(tactic| opt_eval $h:ident [$ts,*]) => `(tactic|
      (opt_norm $h [$ts,*]; repeat (opt_unfold $h; opt_norm $h [$ts,*])))

end Opt.Proof
