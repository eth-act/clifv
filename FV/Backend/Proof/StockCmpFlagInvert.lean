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
private theorem invert (ctx : Ctx) (st : State) (condition : Cond) :
    Stock.externCtor ctx T.invert_cond [.data 96 condition.idx []] st =
      .ok (.data 96 condition.invert.idx [],st) := by
  rw [stock_ctor_baseOnly ctx T.invert_cond _ st (by decide)]
  have call := (ctor_invert_cond_iff (ctx := ctx) (st := st.base) (.data 96 condition.idx [])
    (.data 96 condition.invert.idx []) st.base).mpr ⟨condition,by rw [V.cond?_data,cond_ofIdx_idx],rfl,rfl⟩
  rw [call]
/-- Actual inversion of an explicit flag condition preserves its producer and
all Stock fields while deriving the inverted condition internally. -/
theorem stock_cmp_flag_invert {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (producer : V) (condition : Cond)
    (st : State) (tr : Array RuleId) (n : Nat) :
    (applyTerm p (Stock.sem ctx) cfg (n+40) 123 649 [.data 123 2 [producer,.data 96 condition.idx []]]).run
      (st,tr) = .ok (some (.data 123 2 [producer,.data 96 condition.invert.idx []]),st,tr.push rule_inst_4956.id) := by
  have call := fun q => invert ctx q condition
  cases hp
  isel_eval [*,rule_inst_4954,rule_inst_4955,rule_inst_4956,rule_inst_4957,rule_inst_4959,
    sem_ctor,sem_mkData,sem_unData]
/-- Real successful flag inversion derives its exact output and unchanged complete state. -/
theorem stock_cmp_flag_invert_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {fuel : Nat} (enough : 39 ≤ fuel) (producer : V) (condition : Cond)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) {} fuel 123 649 [.data 123 2 [producer,.data 96 condition.idx []]]
      (st,tr) out (next,trace)) : out = .data 123 2 [producer,.data 96 condition.invert.idx []] ∧ next = st := by
  obtain ⟨n,equal⟩ : ∃ n,fuel+1=n+40 := ⟨fuel-39,by omega⟩
  unfold ApplyInternal at run
  rw [equal,stock_cmp_flag_invert hp ctx rfl producer condition st tr n] at run
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at run
  exact ⟨run.1.symm,run.2.1.symm⟩
/-- All condition variants inhabit the real full-state flag inversion helper. -/
theorem stock_cmp_flag_invert_witness (condition : Cond) :
    ∃ out trace,ApplyInternal program (Stock.sem sinkCtx) {} 999 123 649
      [.data 123 2 [.data 47 1 [],.data 96 condition.idx []]] (sinkState,#[]) out (sinkState,trace) := by
  exact ⟨_,_,stock_cmp_flag_invert data_program sinkCtx (cfg := {}) rfl (.data 47 1 []) condition sinkState #[] 960⟩
end Backend.Stock.Proof.ScalarCmp
