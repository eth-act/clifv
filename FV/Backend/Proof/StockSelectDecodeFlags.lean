module

public import FV.Backend.Proof.StockCmpWithFlags
public import FV.Backend.Proof.StockExtendRequests

@[expose] public section

namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_unData (ctx : Ctx) (ty t k : Nat) (vs : List V) :
    (Stock.sem ctx).unData ty (.data t k vs) = if t = ty then some (k,vs) else none :=
  Backend.Proof.sem_unData ctx ty t k vs
private theorem emit_iff (ctx : Ctx) (st : State) (mi out : V) (next : State) :
    Stock.externCtor ctx T.emit [mi] st = .ok (out,next) ↔
      ∃ m,MInst.ofV mi = some m ∧ out = .op .unit ∧ next = {st with base := st.base.emit m} := by
  rw [stock_ctor_baseOnly ctx T.emit _ st (by decide)]
  have shape : Backend.externCtor ctx T.emit [mi] st.base = match MInst.ofV mi with
      | some m => .ok (.op .unit,st.base.emit m)
      | none => .unmodeled s!"emit of {((mi.variant?).map (·.2.1)).getD "?"}" := rfl
  rw [shape]
  cases decoded : MInst.ofV mi with
  | none => simp
  | some m => simp only [ExtResult.ok.injEq,Prod.mk.injEq,Option.some.injEq]
              constructor
              · intro equal; exact ⟨m,rfl,equal.1.symm,equal.2.symm⟩
              · rintro ⟨m',same,output,state⟩
                cases same
                exact ⟨output.symm,state.symm⟩
private theorem value_reg (ctx : Ctx) (r : Reg) (st : State) :
    Stock.externCtor ctx T.value_reg [.reg r] st = .ok (.regs [r],st) := by
  rw [stock_ctor_baseOnly ctx T.value_reg _ st (by decide)]
  rfl
/-- Successful actual with_flags derives both emitted instruction decoders and
the complete Stock state; no producer/consumer decoder premise is supplied. -/
theorem stock_select_with_flags_decoded {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel : Nat} (enough : 79 ≤ fuel) {mi ci : V} {r : Reg}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg fuel 22 254 [.data 47 1 [mi],.data 49 3 [ci,.reg r]]
      (st,tr) out (next,trace)) :
    ∃ m1 m2,MInst.ofV mi = some m1 ∧ MInst.ofV ci = some m2 ∧ out = .regs [r] ∧
      next = {st with base := (st.base.emit m1).emit m2} := by
  stock_split hp hc run 254
  all_goals isel_inv [*,rule_prelude_lower_789,rule_prelude_lower_798,rule_prelude_lower_807,rule_prelude_lower_812,rule_prelude_lower_818,rule_prelude_lower_829,rule_prelude_lower_837,rule_prelude_lower_850,rule_prelude_lower_864,rule_prelude_lower_881,rule_prelude_lower_903,rule_prelude_lower_912,rule_prelude_lower_927,rule_prelude_lower_943,rule_prelude_lower_951,rule_prelude_lower_965,sem_unData,stock_matchArgs] at hm
  all_goals isel_destruct
  all_goals subst_vars
  all_goals isel_inv [*,rule_prelude_lower_818,sem_ctor,emit_iff,value_reg,stock_matchArgs] at he
  all_goals simp only [emit_iff,value_reg,ExtResult.ok.injEq,Prod.mk.injEq] at *
  all_goals isel_destruct
  all_goals subst_vars
  all_goals rename_i m1 m2 decodedProducer decodedConsumer
  all_goals exact ⟨m1,decodedProducer,m2,decodedConsumer,rfl,rfl⟩
/-- A real compare/csel helper call inhabits decoder extraction while retaining
all scheduling fields, independently of source-operand classification. -/
theorem stock_select_with_flags_decoded_witness :
    ∃ next trace,ApplyInternal program (Stock.sem sinkCtx) {} 999 22 254
      [.data 47 1 [.data 58 2 [.data 59 10 [],.data 93 1 [],.reg .xzr,.reg (.vreg 1 .int),.reg (.vreg 1 .int)]],
        .data 49 3 [.data 58 31 [.reg (.vreg 4 .int),.data 96 Cond.eq.idx [],.reg (.vreg 1 .int),.reg (.vreg 3 .int)],
          .reg (.vreg 4 .int)]] (sinkState,#[]) (.regs [.vreg 4 .int]) (next,trace) := by
  exact ⟨_,_,ScalarCmp.stock_cmp_with_flags_reg data_program sinkCtx (cfg := {}) rfl sinkState #[] 950
    (show MInst.ofV (.data 58 2 [.data 59 10 [],.data 93 1 [],.reg .xzr,.reg (.vreg 1 .int),.reg (.vreg 1 .int)]) =
      some (.aluRRR .subS .size64 .xzr (.vreg 1 .int) (.vreg 1 .int)) from rfl)
    (show MInst.ofV (.data 58 31 [.reg (.vreg 4 .int),.data 96 Cond.eq.idx [],.reg (.vreg 1 .int),.reg (.vreg 3 .int)]) =
      some (.csel (.vreg 4 .int) (.vreg 1 .int) (.vreg 3 .int) .eq) from rfl) (.vreg 4 .int)⟩
end Backend.Stock.Proof.ScalarSelect
