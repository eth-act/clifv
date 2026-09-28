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

set_option hygiene false in
/-- One step of `opt_eval at h`: unfold the first closed interpreter call in `h`. -/
macro "opt_unfold " h:ident : tactic => `(tactic| first
  | rw [Isle.Interp.evalExprN.eq_7] at $h:ident | rw [Isle.Interp.evalExprN.eq_2] at $h:ident
  | rw [Isle.Interp.evalExprN.eq_3] at $h:ident | rw [Isle.Interp.evalExprN.eq_4] at $h:ident
  | rw [Isle.Interp.evalExprN.eq_5] at $h:ident | rw [Isle.Interp.evalExprN.eq_6] at $h:ident
  | rw [Isle.Interp.evalArgsN.eq_2] at $h:ident | rw [Isle.Interp.evalArgsN.eq_3] at $h:ident
  | rw [Isle.Interp.evalBindsN.eq_2] at $h:ident | rw [Isle.Interp.evalBindsN.eq_3] at $h:ident
  | rw [Isle.Interp.applyTermN.eq_2] at $h:ident
  | rw [Isle.Interp.matchIfLetsN.eq_2] at $h:ident | rw [Isle.Interp.matchIfLetsN.eq_3] at $h:ident
  | rw [Isle.Interp.applyTerm.eq_2] at $h:ident
  | rw [Isle.Interp.selectRule.eq_3] at $h:ident | rw [Isle.Interp.selectRule.eq_2] at $h:ident
  | rw [Isle.Interp.tryRule.eq_2] at $h:ident
  | rw [Isle.Interp.matchRule.eq_2] at $h:ident
  | rw [Isle.Interp.matchIfLets.eq_2] at $h:ident | rw [Isle.Interp.matchIfLets.eq_3] at $h:ident
  | rw [Isle.Interp.evalExpr.eq_7] at $h:ident | rw [Isle.Interp.evalExpr.eq_2] at $h:ident
  | rw [Isle.Interp.evalExpr.eq_3] at $h:ident | rw [Isle.Interp.evalExpr.eq_4] at $h:ident
  | rw [Isle.Interp.evalExpr.eq_5] at $h:ident | rw [Isle.Interp.evalExpr.eq_6] at $h:ident
  | rw [Isle.Interp.evalArgs.eq_2] at $h:ident | rw [Isle.Interp.evalArgs.eq_3] at $h:ident
  | rw [Isle.Interp.evalBinds.eq_2] at $h:ident | rw [Isle.Interp.evalBinds.eq_3] at $h:ident
  | rw [Isle.Interp.matchArgs.eq_1] at $h:ident | rw [Isle.Interp.matchArgs.eq_2] at $h:ident
  | rw [Isle.Interp.matchPat.eq_1] at $h:ident | rw [Isle.Interp.matchPat.eq_2] at $h:ident
  | rw [Isle.Interp.matchPat.eq_3] at $h:ident | rw [Isle.Interp.matchPat.eq_4] at $h:ident
  | rw [Isle.Interp.matchPat.eq_5] at $h:ident | rw [Isle.Interp.matchPat.eq_6] at $h:ident
  | rw [Isle.Interp.matchPat.eq_7] at $h:ident | rw [Isle.Interp.matchPat.eq_8] at $h:ident
  | rw [Isle.Interp.matchPatN.eq_1] at $h:ident | rw [Isle.Interp.matchPatN.eq_2] at $h:ident
  | rw [Isle.Interp.matchPatN.eq_3] at $h:ident | rw [Isle.Interp.matchPatN.eq_4] at $h:ident
  | rw [Isle.Interp.matchPatN.eq_5] at $h:ident | rw [Isle.Interp.matchPatN.eq_6] at $h:ident
  | rw [Isle.Interp.matchPatN.eq_7] at $h:ident | rw [Isle.Interp.matchPatN.eq_8] at $h:ident
  | rw [Isle.Interp.matchArgsN.eq_1] at $h:ident | rw [Isle.Interp.matchArgsN.eq_2] at $h:ident)

/-- Normalise between steps: data/constructor facts and monad laws (separate passes). -/
syntax "opt_norm " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
macro_rules
  | `(tactic| opt_norm $h:ident) => `(tactic| opt_norm $h [])
  | `(tactic| opt_norm $h:ident [$ts,*]) => `(tactic|
      repeat (first
        | simp (disch := assumption) only [opt_data, $ts,*] at $h:ident
        | simp (disch := assumption) only [opt_monad, opt_imm, $ts,*] at $h:ident))

/-- Evaluate the interpreter call in hypothesis `h`: alternate `opt_unfold` and `opt_norm`. -/
syntax "opt_eval " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
macro_rules
  | `(tactic| opt_eval $h:ident) => `(tactic| opt_eval $h [])
  | `(tactic| opt_eval $h:ident [$ts,*]) => `(tactic|
      (opt_norm $h [$ts,*]; repeat (opt_unfold $h; opt_norm $h [$ts,*])))

end Opt.Proof
