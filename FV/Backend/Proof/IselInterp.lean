import FV.Backend.Proof.IselData

/-!
# Evaluating the ISLE interpreter in proofs

The interpreter (`FV/Isle/Interp.lean`) is a fuel-indexed mutual recursion in the monad
`M σ = StateT (σ × Array RuleId) (Except Err)`. Proofs about one rule evaluate it on
concrete rule data but a *symbolic* lowering context (the CLIF instruction, its operands and
their registers are variables). Plain `simp [evalExpr, applyTerm, …]` does not work for that:
`simp` rewrites under binders, so it also unfolds the interpreter inside every not-yet-taken
continuation (`fun env => …`), once per unit of fuel; the term grows exponentially and the
process ran out of memory (8 GB in 18 s on a two-rule term).

`isel_eval` instead evaluates *outermost-closed-call first*: it unfolds one interpreter call
with `rw` (which never rewrites a subterm containing a bound variable, so continuations are
left alone until their argument is known) and then normalises with `simp only` over the monad
laws below, the generated data facts (`isel_data`) and caller-supplied lemmas — a simp set
with no interpreter equations, so nothing is unfolded under a binder. Each round exposes the
next closed call. The kernel never sees `Isle.Aarch64.program`: `termOf`/`rulesOf` are
rewritten with the `native_decide` facts of `IselData`.
-/

namespace Backend.Proof

open Isle Isle.Interp

/-! ## Monad laws in the form the interpreter's `do` blocks produce -/

section Monad
variable {σ α β ε : Type}

@[isel_monad] theorem except_ok_bind (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f : Except ε β) = f a := rfl
@[isel_monad] theorem except_pure (a : α) : (pure a : Except ε α) = .ok a := rfl
@[isel_monad] theorem run_liftM (e : Except Err α) (s : σ × Array RuleId) :
    (liftM e : M σ α).run s = (e >>= fun a => Except.ok (a, s)) := by
  cases e <;> rfl
@[isel_monad] theorem run_pure' (a : α) (s : σ × Array RuleId) :
    (pure a : M σ α).run s = .ok (a, s) := rfl
@[isel_monad] theorem run_bind' (x : M σ α) (f : α → M σ β) (s : σ × Array RuleId) :
    (x >>= f).run s = (x.run s >>= fun p => (f p.1).run p.2) := rfl
@[isel_monad] theorem run_get' (s : σ × Array RuleId) :
    (get : M σ (σ × Array RuleId)).run s = .ok (s, s) := rfl
@[isel_monad] theorem run_set' (s s' : σ × Array RuleId) :
    (set s' : M σ PUnit).run s = .ok (⟨⟩, s') := rfl
@[isel_monad] theorem run_throw' (e : Err) (s : σ × Array RuleId) :
    (throw e : M σ α).run s = .error e := rfl
@[isel_monad] theorem run_fire (r : RuleId) (st : σ) (tr : Array RuleId) :
    (fire r : M σ Unit).run (st, tr) = Except.ok ((), (st, tr.push r)) := rfl

end Monad

attribute [isel_monad] Bool.false_eq_true ite_true ite_false dite_true dite_false
  List.length_cons List.length_nil Nat.zero_add Nat.reduceAdd Array.size_replicate
  Array.set!_eq_setIfInBounds beq_self_eq_true Nat.lt_irrefl decide_true decide_false
  Option.some.injEq reduceIte reduceDIte bne_self_eq_false Bool.not_false Bool.not_true
  Bool.and_true Bool.true_and Bool.and_false Bool.false_and Nat.reduceLT Nat.reduceLeDiff
  Nat.reduceEqDiff Nat.reduceBEq Nat.reduceBNe Nat.reduceSub Nat.lt_add_one Nat.zero_lt_succ


set_option hygiene false in
/-- One round of `isel_eval`: unfold the first closed interpreter call. -/
macro "isel_unfold" : tactic => `(tactic| first
      | rw [Isle.Interp.applyTerm.eq_2] | rw [Isle.Interp.selectRule.eq_3] | rw [Isle.Interp.selectRule.eq_2] | rw [Isle.Interp.tryRule.eq_2]
      | rw [Isle.Interp.matchRule.eq_2] | rw [Isle.Interp.matchIfLets.eq_2] | rw [Isle.Interp.matchIfLets.eq_3]
      | rw [Isle.Interp.evalExpr.eq_2] | rw [Isle.Interp.evalExpr.eq_3] | rw [Isle.Interp.evalExpr.eq_4] | rw [Isle.Interp.evalExpr.eq_5]
      | rw [Isle.Interp.evalExpr.eq_6] | rw [Isle.Interp.evalExpr.eq_7]
      | rw [Isle.Interp.evalArgs.eq_2] | rw [Isle.Interp.evalArgs.eq_3] | rw [Isle.Interp.evalBinds.eq_2] | rw [Isle.Interp.evalBinds.eq_3]
      | rw [Isle.Interp.matchArgs.eq_1] | rw [Isle.Interp.matchArgs.eq_2]
      | rw [Isle.Interp.matchPat.eq_1] | rw [Isle.Interp.matchPat.eq_2] | rw [Isle.Interp.matchPat.eq_3] | rw [Isle.Interp.matchPat.eq_4]
      | rw [Isle.Interp.matchPat.eq_5] | rw [Isle.Interp.matchPat.eq_6] | rw [Isle.Interp.matchPat.eq_7] | rw [Isle.Interp.matchPat.eq_8]
      | rw [Isle.Interp.matchAll.eq_1] | rw [Isle.Interp.matchAll.eq_2])

/-- Normalise between interpreter steps: data facts and monad laws in separate `simp only`
passes (one pass mixing both produced proofs whose kernel check unfolded `program`). -/
syntax "isel_norm" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| isel_norm) => `(tactic| isel_norm [])
  | `(tactic| isel_norm [$ts,*]) => `(tactic|
      repeat (first | simp only [isel_data, $ts,*] | simp only [isel_monad, $ts,*]))

/-- Evaluate the interpreter on the goal: alternate `isel_unfold` and `isel_norm`. -/
syntax "isel_eval" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| isel_eval) => `(tactic| isel_eval [])
  | `(tactic| isel_eval [$ts,*]) => `(tactic| repeat (isel_unfold; isel_norm [$ts,*]))

end Backend.Proof
