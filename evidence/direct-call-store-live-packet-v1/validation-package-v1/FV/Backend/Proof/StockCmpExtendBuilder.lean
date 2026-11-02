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
private theorem zero (ctx : Ctx) (st : State) :
    Stock.externCtor ctx T.writable_zero_reg [] st = .ok (.reg .xzr,st) := by
  rw [stock_ctor_baseOnly ctx T.writable_zero_reg _ st (by decide)]
  rfl
/-- Actual extended-comparison construction preserves the complete Stock state,
including the source request/sinking fields outside its pure producer builder. -/
theorem stock_cmp_extend_builder {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (st : State) (tr : Array RuleId) (n : Nat) (sz rx ry extension : V) :
    (applyTerm p (Stock.sem ctx) cfg (n+40) 47 393 [sz,rx,ry,extension]).run (st,tr) =
      .ok (some (.data 47 1 [.data 58 8 [.data 59 10 [],sz,.reg .xzr,rx,ry,extension]]),
        st,tr.push rule_inst_2786.id) := by
  have register := zero ctx st
  cases hp
  isel_eval [*,rule_inst_2786,sem_ctor,sem_mkData]
/-- Successful actual extended-comparison construction derives its exact
producer and full unchanged state internally. -/
theorem stock_cmp_extend_builder_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel : Nat} (enough : 39 ≤ fuel)
    {st next : State} {tr trace : Array RuleId} {sz rx ry extension out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg fuel 47 393 [sz,rx,ry,extension] (st,tr) out (next,trace)) :
    out = .data 47 1 [.data 58 8 [.data 59 10 [],sz,.reg .xzr,rx,ry,extension]] ∧ next = st := by
  obtain ⟨n,equal⟩ : ∃ n,fuel+1=n+40 := ⟨fuel-39,by omega⟩
  unfold ApplyInternal at run
  rw [equal,stock_cmp_extend_builder hp ctx hc] at run
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at run
  exact ⟨run.1.symm,run.2.1.symm⟩
/-- A real extended-comparison producer with sparse register numbers inhabits
the builder and successful-execution observation contracts. -/
theorem stock_cmp_extend_builder_witness :
    ∃ out trace,ApplyInternal program (Stock.sem sinkCtx) {} 999 47 393
      [.data 93 0 [],.reg (.vreg 7 .int),.reg (.vreg 31 .int),.data 84 5 []]
      (sinkState,#[]) out (sinkState,trace) ∧
      out = .data 47 1 [.data 58 8 [.data 59 10 [],.data 93 0 [],.reg .xzr,
        .reg (.vreg 7 .int),.reg (.vreg 31 .int),.data 84 5 []]] := by
  exact ⟨_,_,stock_cmp_extend_builder data_program sinkCtx rfl sinkState #[] 960 _ _ _ _,rfl⟩
end Backend.Stock.Proof.ScalarCmp
