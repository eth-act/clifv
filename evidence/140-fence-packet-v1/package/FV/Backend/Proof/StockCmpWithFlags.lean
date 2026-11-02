import FV.Backend.Proof.StockProjection
import FV.Backend.Proof.IselCtlTry
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
private theorem compact_skip_789 {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (fuel : Nat) (initial : State × Array RuleId) (mi ci : V) (r : Reg) :
    (matchRule p (Stock.sem ctx) cfg fuel rule_prelude_lower_789
      [.data 47 1 [mi],.data 49 3 [ci,.reg r]]).run initial =
      (match fuel with | 0 => .error .outOfFuel | _ + 1 => .ok (none,initial)) := by
  rcases initial with ⟨st,tr⟩
  cases fuel with
  | zero => rfl
  | succ n =>
    have lookup := hp.t1794
    isel_eval [lookup,rule_prelude_lower_789,sem_unData]

private theorem compact_skip_798 {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (fuel : Nat) (initial : State × Array RuleId) (mi ci : V) (r : Reg) :
    (matchRule p (Stock.sem ctx) cfg fuel rule_prelude_lower_798
      [.data 47 1 [mi],.data 49 3 [ci,.reg r]]).run initial =
      (match fuel with | 0 => .error .outOfFuel | _ + 1 => .ok (none,initial)) := by
  rcases initial with ⟨st,tr⟩
  cases fuel with
  | zero => rfl
  | succ n =>
    have lookup := hp.t1794
    isel_eval [lookup,rule_prelude_lower_798,sem_unData]

private theorem compact_skip_807 {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (fuel : Nat) (initial : State × Array RuleId) (mi ci : V) (r : Reg) :
    (matchRule p (Stock.sem ctx) cfg fuel rule_prelude_lower_807
      [.data 47 1 [mi],.data 49 3 [ci,.reg r]]).run initial =
      (match fuel with | 0 => .error .outOfFuel | _ + 1 => .ok (none,initial)) := by
  rcases initial with ⟨st,tr⟩
  cases fuel with
  | zero => rfl
  | succ n =>
    have lookup := hp.t1794
    isel_eval [lookup,rule_prelude_lower_807,sem_unData]

private theorem compact_skip_812 {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (fuel : Nat) (initial : State × Array RuleId) (mi ci : V) (r : Reg) :
    (matchRule p (Stock.sem ctx) cfg fuel rule_prelude_lower_812
      [.data 47 1 [mi],.data 49 3 [ci,.reg r]]).run initial =
      (match fuel with | 0 => .error .outOfFuel | _ + 1 => .ok (none,initial)) := by
  rcases initial with ⟨st,tr⟩
  cases fuel with
  | zero => rfl
  | succ n =>
    have lookup := hp.t1793
    isel_eval [lookup,rule_prelude_lower_812,sem_unData]

private def compact_flags_env (mi ci : V) (r : Reg) : Isle.Interp.Env V :=
  (((Array.replicate 5 none).set! 0 (some mi)).set! 1 (some ci)).set! 2 (some (.reg r))

private theorem compact_match_818 {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (fuel : Nat) (initial : State × Array RuleId) (mi ci : V) (r : Reg) :
    (matchRule p (Stock.sem ctx) cfg fuel rule_prelude_lower_818
      [.data 47 1 [mi],.data 49 3 [ci,.reg r]]).run initial =
      (match fuel with
       | 0 => .error .outOfFuel
       | 1 => .error .outOfFuel
       | _ + 2 => .ok (some (compact_flags_env mi ci r),initial)) := by
  rcases initial with ⟨st,tr⟩
  have producer := hp.t1791
  have consumer := hp.t1802
  cases fuel with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => isel_eval [producer,consumer,rule_prelude_lower_818,sem_unData,compact_flags_env,matchIfLets.eq_1]
    | succ n => isel_eval [producer,consumer,rule_prelude_lower_818,sem_unData,compact_flags_env]

private theorem compact_rhs_818 {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (st : State) (tr : Array RuleId) (n : Nat) (mi ci : V) (m1 m2 : MInst)
    (producer : MInst.ofV mi = some m1) (consumer : MInst.ofV ci = some m2) (r : Reg) :
    (evalExpr p (Stock.sem ctx) cfg (n+49) rule_prelude_lower_818.rhs
      (compact_flags_env mi ci r)).run (st,tr) =
      .ok (some (.regs [r]),{st with base := (st.base.emit m1).emit m2},tr) := by
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
  have emitLookup := hp.t235
  have valueLookup := hp.t164
  isel_eval [emitLookup,valueLookup,rule_prelude_lower_818,compact_flags_env,sem_ctor,emitProducer,emitConsumer,value]

private theorem compact_skip_789M {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (fuel : Nat) (mi ci : V) (r : Reg) :
    matchRule p (Stock.sem ctx) cfg fuel rule_prelude_lower_789
      [.data 47 1 [mi],.data 49 3 [ci,.reg r]] =
      (match fuel with | 0 => throw .outOfFuel | _ + 1 => pure none) := by
  funext initial
  cases fuel with
  | zero => rfl
  | succ k => exact compact_skip_789 hp ctx cfg (k+1) initial mi ci r

private theorem compact_skip_798M {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (fuel : Nat) (mi ci : V) (r : Reg) :
    matchRule p (Stock.sem ctx) cfg fuel rule_prelude_lower_798
      [.data 47 1 [mi],.data 49 3 [ci,.reg r]] =
      (match fuel with | 0 => throw .outOfFuel | _ + 1 => pure none) := by
  funext initial
  cases fuel with
  | zero => rfl
  | succ k => exact compact_skip_798 hp ctx cfg (k+1) initial mi ci r

private theorem compact_skip_807M {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (fuel : Nat) (mi ci : V) (r : Reg) :
    matchRule p (Stock.sem ctx) cfg fuel rule_prelude_lower_807
      [.data 47 1 [mi],.data 49 3 [ci,.reg r]] =
      (match fuel with | 0 => throw .outOfFuel | _ + 1 => pure none) := by
  funext initial
  cases fuel with
  | zero => rfl
  | succ k => exact compact_skip_807 hp ctx cfg (k+1) initial mi ci r

private theorem compact_skip_812M {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (fuel : Nat) (mi ci : V) (r : Reg) :
    matchRule p (Stock.sem ctx) cfg fuel rule_prelude_lower_812
      [.data 47 1 [mi],.data 49 3 [ci,.reg r]] =
      (match fuel with | 0 => throw .outOfFuel | _ + 1 => pure none) := by
  funext initial
  cases fuel with
  | zero => rfl
  | succ k => exact compact_skip_812 hp ctx cfg (k+1) initial mi ci r

private theorem compact_match_818M {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (fuel : Nat) (mi ci : V) (r : Reg) :
    matchRule p (Stock.sem ctx) cfg fuel rule_prelude_lower_818
      [.data 47 1 [mi],.data 49 3 [ci,.reg r]] =
      (match fuel with
       | 0 => throw .outOfFuel
       | 1 => throw .outOfFuel
       | _ + 2 => pure (some (compact_flags_env mi ci r))) := by
  funext initial
  cases fuel with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => exact compact_match_818 hp ctx cfg 1 initial mi ci r
    | succ k => exact compact_match_818 hp ctx cfg (k+2) initial mi ci r

private theorem compact_rhs_818M {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (n : Nat) (mi ci : V) (m1 m2 : MInst)
    (producer : MInst.ofV mi = some m1) (consumer : MInst.ofV ci = some m2) (r : Reg) :
    evalExpr p (Stock.sem ctx) cfg (n+49) rule_prelude_lower_818.rhs
      (compact_flags_env mi ci r) =
      (fun initial => .ok (some (.regs [r]),
        {initial.1 with base := (initial.1.base.emit m1).emit m2},initial.2)) := by
  funext initial
  rcases initial with ⟨st,tr⟩
  exact compact_rhs_818 hp ctx cfg st tr n mi ci m1 m2 producer consumer r

private theorem compact_try_789 {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (n : Nat) (mi ci : V) (r : Reg) :
    tryRule p (Stock.sem ctx) cfg (n+2) rule_prelude_lower_789
      [.data 47 1 [mi],.data 49 3 [ci,.reg r]] = pure none := by
  rw [tryRule.eq_2,compact_skip_789M hp ctx cfg]
  rfl

private theorem compact_try_798 {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (n : Nat) (mi ci : V) (r : Reg) :
    tryRule p (Stock.sem ctx) cfg (n+2) rule_prelude_lower_798
      [.data 47 1 [mi],.data 49 3 [ci,.reg r]] = pure none := by
  rw [tryRule.eq_2,compact_skip_798M hp ctx cfg]
  rfl

private theorem compact_try_807 {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (n : Nat) (mi ci : V) (r : Reg) :
    tryRule p (Stock.sem ctx) cfg (n+2) rule_prelude_lower_807
      [.data 47 1 [mi],.data 49 3 [ci,.reg r]] = pure none := by
  rw [tryRule.eq_2,compact_skip_807M hp ctx cfg]
  rfl

private theorem compact_try_812 {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (n : Nat) (mi ci : V) (r : Reg) :
    tryRule p (Stock.sem ctx) cfg (n+2) rule_prelude_lower_812
      [.data 47 1 [mi],.data 49 3 [ci,.reg r]] = pure none := by
  rw [tryRule.eq_2,compact_skip_812M hp ctx cfg]
  rfl

private theorem compact_try_818 {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (n : Nat) (mi ci : V) (r : Reg) :
    tryRule p (Stock.sem ctx) cfg (n+3) rule_prelude_lower_818
      [.data 47 1 [mi],.data 49 3 [ci,.reg r]] = pure (some (compact_flags_env mi ci r)) := by
  rw [tryRule.eq_2,compact_match_818M hp ctx cfg]
  rfl

private theorem compact_select_prefix {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (hc : cfg.checkOverlap = false) (n : Nat) (term : Term) (tail : List Rule)
    (mi ci : V) (r : Reg) :
    selectRule p (Stock.sem ctx) cfg (n+49) term
      ([rule_prelude_lower_789,rule_prelude_lower_798,rule_prelude_lower_807,
        rule_prelude_lower_812,rule_prelude_lower_818] ++ tail)
      [.data 47 1 [mi],.data 49 3 [ci,.reg r]] =
      pure (some (rule_prelude_lower_818,compact_flags_env mi ci r)) := by
  simp only [List.cons_append,List.nil_append]
  rw [selectRule.eq_3,compact_try_789 hp ctx cfg (n+46) mi ci r]
  change selectRule p (Stock.sem ctx) cfg (n+48) term
    ([rule_prelude_lower_798,rule_prelude_lower_807,rule_prelude_lower_812,rule_prelude_lower_818] ++ tail)
    [.data 47 1 [mi],.data 49 3 [ci,.reg r]] = _
  simp only [List.cons_append,List.nil_append]
  rw [selectRule.eq_3,compact_try_798 hp ctx cfg (n+45) mi ci r]
  change selectRule p (Stock.sem ctx) cfg (n+47) term
    ([rule_prelude_lower_807,rule_prelude_lower_812,rule_prelude_lower_818] ++ tail)
    [.data 47 1 [mi],.data 49 3 [ci,.reg r]] = _
  simp only [List.cons_append,List.nil_append]
  rw [selectRule.eq_3,compact_try_807 hp ctx cfg (n+44) mi ci r]
  change selectRule p (Stock.sem ctx) cfg (n+46) term
    ([rule_prelude_lower_812,rule_prelude_lower_818] ++ tail)
    [.data 47 1 [mi],.data 49 3 [ci,.reg r]] = _
  simp only [List.cons_append,List.nil_append]
  rw [selectRule.eq_3,compact_try_812 hp ctx cfg (n+43) mi ci r]
  change selectRule p (Stock.sem ctx) cfg (n+45) term (rule_prelude_lower_818 :: tail)
    [.data 47 1 [mi],.data 49 3 [ci,.reg r]] = _
  rw [selectRule.eq_3,compact_try_818 hp ctx cfg (n+41) mi ci r]
  simp only [hc,Bool.false_eq_true,ite_false]
  rfl

/-- The actual side-effect flag producer/register consumer path emits both
instructions and retains all scheduling fields; no pure-full-closure claim. -/
theorem stock_cmp_with_flags_reg {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (st : State) (tr : Array RuleId) (n : Nat)
    {mi ci : V} {m1 m2 : MInst} (producer : MInst.ofV mi = some m1) (consumer : MInst.ofV ci = some m2) (r : Reg) :
    (applyTerm p (Stock.sem ctx) cfg (n+50) 22 254 [.data 47 1 [mi],.data 49 3 [ci,.reg r]]).run (st,tr) =
      .ok (some (.regs [r]),{st with base := (st.base.emit m1).emit m2},tr.push rule_prelude_lower_818.id) := by
  rw [applyTerm.eq_2]
  isel_norm [hp.t254]
  have selection := compact_select_prefix hp ctx cfg hc n T.with_flags
    [rule_prelude_lower_829,rule_prelude_lower_837,rule_prelude_lower_850,
     rule_prelude_lower_864,rule_prelude_lower_881,rule_prelude_lower_903,
     rule_prelude_lower_912,rule_prelude_lower_927,rule_prelude_lower_943,
     rule_prelude_lower_951,rule_prelude_lower_965] mi ci r
  simp only [List.cons_append,List.nil_append] at selection
  rw [hp.r254,selection]
  isel_norm []
  rw [compact_rhs_818M hp ctx cfg n mi ci m1 m2 producer consumer r]
  isel_norm []
  rfl

end Backend.Stock.Proof.ScalarCmp
