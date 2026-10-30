import FV.Backend.Proof.StockPolicy
import FV.Backend.Proof.IselCtlTry

namespace Backend.Stock.Proof.ScalarMask
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl

private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl

private theorem sem_i64 (ctx : Ctx) :
    (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl

private theorem sem_unData (ctx : Ctx) (ty t k : Nat) (vs : List V) :
    (Stock.sem ctx).unData ty (.data t k vs) = if t = ty then some (k,vs) else none :=
  Backend.Proof.sem_unData ctx ty t k vs

set_option maxHeartbeats 4000000 in
/-- The actual CSETM consumer allocates its result while retaining the complete
Stock scheduling state. Its instruction is emitted by the enclosing flags helper. -/
theorem stock_csetm_helper {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (condition : V) (st : State)
    (trace : Array RuleId) (n : Nat) :
    (applyTerm p (Stock.sem ctx) cfg (n+30) 49 428 [condition]).run (st,trace) =
      .ok (some (.data 49 3 [
        .data 58 34 [.reg (st.base.fresh .int).1,condition],
        .reg (st.base.fresh .int).1]),
        {st with base := (st.base.fresh .int).2},trace.push rule_inst_3082.id) := by
  have temp (s : State) : Stock.externCtor ctx T.«temp_writable_reg» [.ty (.int 64)] s =
      .ok (.reg (s.base.fresh .int).1,{s with base := (s.base.fresh .int).2}) := rfl
  have reg (r : Reg) (s : State) : Stock.externCtor ctx T.«writable_reg_to_reg» [.reg r] s =
      .ok (.reg r,s) := rfl
  cases hp
  isel_eval [*,rule_inst_3082,sem_ctor,sem_mkData,sem_unData,sem_i64,temp,reg]

/-- An actual successful helper call determines its consumer and complete
post-allocation state without a caller-supplied emission equation. -/
theorem stock_csetm_helper_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {cfg : Config} (hc : cfg.checkOverlap = false) {fuel : Nat} (enough : 29 ≤ fuel)
    (condition : V) {st next : State} {before trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg fuel 49 428 [condition]
      (st,before) out (next,trace)) :
    out = .data 49 3 [.data 58 34 [.reg (st.base.fresh .int).1,condition],
      .reg (st.base.fresh .int).1] ∧ next = {st with base := (st.base.fresh .int).2} := by
  obtain ⟨n,equal⟩ : ∃ n,fuel+1=n+30 := ⟨fuel-29,by omega⟩
  unfold ApplyInternal at run
  rw [equal,stock_csetm_helper hp ctx hc condition st before n] at run
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at run
  exact ⟨run.1.symm,run.2.1.symm⟩

/-- A real condition and real fresh register inhabit the helper contract. -/
theorem stock_csetm_helper_witness :
    ∃ out next trace,
      (applyTerm program (Stock.sem sinkCtx) {} 1000 49 428 [.data 96 1 []]).run
        (sinkState,#[]) = .ok (some out,next,trace) ∧
        (V.data 96 1 []).cond? = some .ne := by
  exact ⟨_,_,_,stock_csetm_helper data_program sinkCtx (cfg := {}) rfl
    (.data 96 1 []) sinkState #[] 970,rfl⟩

end Backend.Stock.Proof.ScalarMask
