import FV.Backend.Proof.StockAcquirePendingTrace
import FV.Backend.Proof.StockAcquireSinkReceipts
import FV.Backend.Proof.StockRequestSuccess

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
attribute [local irreducible] Isle.Aarch64.program

/-- The real atomic sink RHS contributes precisely its bound producer.
The address request retains the resulting sink state. -/
theorem sink_atomic_rhs_pending {ctx : Ctx} {st next : State} {before after : Array RuleId}
    {bound : Isle.Interp.Env V} {producer n : Nat} {out : V}
    (producerValue : bound[1]? = some (some (.inst producer)))
    (run : (evalExpr program (Stock.sem ctx) {} (n+20) rule_inst_3905.rhs bound).run
      (st,before) = .ok (some out,next,after)) :
    ∃ middle,Stock.externCtor ctx T.sink_inst [.inst producer] st = .ok (.op .unit,middle) ∧
      PendingSinks ctx st [producer] next ∧ next.sunk = middle.sunk := by
  have ctor (term : Term) (args : List V) (state : State) :
      (Stock.sem ctx).ctor term args state = Stock.externCtor ctx term args state := rfl
  have overlap : ({} : Config).checkOverlap = false := rfl
  isel_inv [*,rule_inst_3905,ctor] at run
  simp only [data_program.t182,data_program.t236,T.put_in_reg,T.sink_inst,pure,Except.pure] at *
  isel_destruct
  subst_vars
  rename_i next middle sinkCall putCall
  have accepted := sink_accepted sinkCall
  have sinkUnit : Stock.externCtor ctx T.sink_inst [.inst producer] st = .ok (.op .unit,middle) := by
    simpa only [accepted.2.2.2.1,T.sink_inst] using sinkCall
  have entries := stock_ctor_entryColor putCall
  have color := stock_ctor_color_without_sink (t := T.put_in_reg)
    (by simp [T.put_in_reg,TId.sink_inst]) putCall
  have sunk := stock_ctor_noSink (t := T.put_in_reg) (by decide) putCall
  exact ⟨middle,sinkUnit,.sink sinkUnit (.frame entries color (.nil next)),sunk⟩

end Backend.Stock.Proof.Acquire810
