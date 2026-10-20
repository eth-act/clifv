import FV.Backend.Proof.StockCmpBuilders
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
private theorem sem_unData (ctx : Ctx) (ty t k : Nat) (vs : List V) :
    (Stock.sem ctx).unData ty (.data t k vs) = if t = ty then some (k,vs) else none :=
  Backend.Proof.sem_unData ctx ty t k vs
section MonadN
variable {σ α β ε : Type}
private theorem except_ok_bind_n (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f : Except ε β) = f a := by rw [Backend.Proof.except_ok_bind]
private theorem except_pure_n (a : α) : (pure a : Except ε α) = .ok a := by rw [Backend.Proof.except_pure]
private theorem except_error_bind_n (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f : Except ε β) = .error e := by rw [Backend.Proof.except_error_bind]
private theorem run_liftM_n (e : Except Err α) (s : σ × Array RuleId) :
    (liftM e : M σ α).run s = (e >>= fun a => Except.ok (a, s)) := by rw [Backend.Proof.run_liftM]
private theorem run_pure'_n (a : α) (s : σ × Array RuleId) :
    (pure a : M σ α).run s = .ok (a, s) := by rw [Backend.Proof.run_pure']
private theorem run_bind'_n (x : M σ α) (f : α → M σ β) (s : σ × Array RuleId) :
    (x >>= f).run s = (x.run s >>= fun p => (f p.1).run p.2) := by rw [Backend.Proof.run_bind']
private theorem run_get'_n (s : σ × Array RuleId) :
    (get : M σ (σ × Array RuleId)).run s = .ok (s, s) := by rw [Backend.Proof.run_get']
private theorem run_set'_n (s s' : σ × Array RuleId) :
    (set s' : M σ PUnit).run s = .ok (⟨⟩, s') := by rw [Backend.Proof.run_set']
private theorem run_throw'_n (e : Err) (s : σ × Array RuleId) :
    (throw e : M σ α).run s = .error e := by rw [Backend.Proof.run_throw']
private theorem run_fire_n (r : RuleId) (st : σ) (tr : Array RuleId) :
    (fire r : M σ Unit).run (st, tr) = Except.ok ((), (st, tr.push r)) := by rw [Backend.Proof.run_fire]
end MonadN
/-! `isel_eval` with the monad laws restated as non-`rfl` theorems: as `rfl` theorems simp
applies them definitionally, and the kernel then re-derives one large definitional step
of this evaluation by unfolding (23 GB). Same rewrites, explicit proofs (2 GB). -/
local syntax "isel_norm_k" ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]") : tactic
local macro_rules
  | `(tactic| isel_norm_k [$ts,*]) => `(tactic|
      repeat (first | simp only [isel_data, $ts,*] | simp only [except_ok_bind_n, except_pure_n, except_error_bind_n, run_liftM_n, run_pure'_n, run_bind'_n, run_get'_n, run_set'_n, run_throw'_n, run_fire_n, Bool.false_eq_true, ite_true, ite_false, dite_true, dite_false, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Array.size_replicate, Array.set!_eq_setIfInBounds, beq_self_eq_true, Nat.lt_irrefl, decide_true, decide_false, Option.some.injEq, reduceIte, reduceDIte, bne_self_eq_false, Bool.not_false, Bool.not_true, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Nat.reduceLT, Nat.reduceLeDiff, Array.size_setIfInBounds, Array.getElem?_setIfInBounds, Array.getElem?_replicate, Nat.reduceEqDiff, Nat.reduceBEq, Nat.reduceBNe, Nat.reduceSub, Nat.lt_add_one, Nat.zero_lt_succ, $ts,*]))
local syntax "isel_eval_k" ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]") : tactic
local macro_rules
  | `(tactic| isel_eval_k [$ts,*]) => `(tactic| (isel_norm_k [$ts,*]; repeat (isel_unfold; isel_norm_k [$ts,*])))
/-- The actual side-effect flag producer/register consumer path emits both
instructions and retains all scheduling fields; no pure-full-closure claim. -/
theorem stock_cmp_with_flags_reg {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (st : State) (tr : Array RuleId) (n : Nat)
    {mi ci : V} {m1 m2 : MInst} (producer : MInst.ofV mi = some m1) (consumer : MInst.ofV ci = some m2) (r : Reg) :
    (applyTerm p (Stock.sem ctx) cfg (n+50) 22 254 [.data 47 1 [mi],.data 49 3 [ci,.reg r]]).run (st,tr) =
      .ok (some (.regs [r]),{st with base := (st.base.emit m1).emit m2},tr.push rule_prelude_lower_818.id) := by
  have emitProducer : ∀ q : State,Stock.externCtor ctx T.emit [mi] q =
      .ok (.op .unit,{q with base := q.base.emit m1}) := by
    intro q
    rw [stock_ctor_baseOnly ctx T.emit [mi] q (by decide),ctor_emit ctx q.base producer]
  have emitConsumer : ∀ q : State,Stock.externCtor ctx T.emit [ci] q =
      .ok (.op .unit,{q with base := q.base.emit m2}) := by
    intro q
    rw [stock_ctor_baseOnly ctx T.emit [ci] q (by decide),ctor_emit ctx q.base consumer]
  have value : ∀ q : State,Stock.externCtor ctx T.value_reg [.reg r] q = .ok (.regs [r],q) := by
    intro q
    rw [stock_ctor_baseOnly ctx T.value_reg [.reg r] q (by decide)]
    rfl
  cases hp
  isel_eval_k [*,rule_prelude_lower_789,rule_prelude_lower_798,rule_prelude_lower_807,rule_prelude_lower_812,rule_prelude_lower_818,stock_matchArgs,sem_ctor,sem_mkData,sem_unData]
end Backend.Stock.Proof.ScalarCmp
