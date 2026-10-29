module

public import FV.Backend.Proof.StockSelectDecodedObserved
public import FV.Backend.Proof.StockCmpCondition

@[expose] public section

namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- A successful actual explicit-flags select supplies a proof-only715 boolean
companion with the same producer and fresh destination. The real state retains
its original demand marks and csel code; no companion instruction is inserted. -/
theorem stock_select_flags_boolean_companion {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel w x y : Nat} (enough : 279 ≤ fuel)
    (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) {mi : V} (condition : Cond)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg fuel 22 659
      [.ty (.int w),.data 123 2 [.data 47 1 [mi],.data 96 condition.idx []],.value x,.value y]
      (st,tr) out (next,trace)) :
    ∃ m rx ry,MInst.ofV mi = some m ∧ DemandAllowed ctx st x ∧ DemandAllowed ctx (st.mark x) y ∧
      ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧ out = .regs [(st.base.fresh .int).1] ∧
      next = {(st.mark x).mark y with base := (((st.base.fresh .int).2.emit m).emit
        (.csel (st.base.fresh .int).1 rx ry condition))} ∧
      ∃ booleanTrace,ApplyInternal p (Stock.sem ctx) cfg 119 27 715
        [.data 123 2 [.data 47 1 [mi],.data 96 condition.idx []]] (st,tr) (.reg (st.base.fresh .int).1)
        ({st with base := (((st.base.fresh .int).2.emit m).emit
          (.cset (st.base.fresh .int).1 condition))},booleanTrace) := by
  obtain ⟨m,decoded,safeX,safeY,rx,ry,mapX,mapY,output,finish⟩ :=
    stock_select_flags_decoded_observed hp ctx hc enough width condition run
  obtain ⟨booleanTrace,booleanRun⟩ := ScalarCmp.stock_cmp_condition_flags hp ctx hc st tr 0 decoded condition
  exact ⟨m,rx,ry,decoded,safeX,safeY,mapX,mapY,output,finish,booleanTrace,booleanRun⟩
end Backend.Stock.Proof.ScalarSelect
