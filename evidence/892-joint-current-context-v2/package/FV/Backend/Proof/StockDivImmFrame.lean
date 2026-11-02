import FV.Backend.Proof.IselCmpInv
import FV.Backend.Proof.StockImm
import FV.Backend.Proof.StockDivImmPure
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Successful real immediate materialization preserves every scheduling field,
including when used for a looked-through divisor. This observation uses only
interpreter projection, independently of the legacy machine-value contracts. -/
theorem stock_div_imm_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {cfg : Config} (hc : cfg.checkOverlap = false) {n : Nat} {args : List V}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg n 27 553 args (st,tr) out (next,trace)) :
    next = {st with base := next.base} ∧
      ApplyInternal p (Backend.sem ctx) cfg n 27 553 args (st.base,tr) out (next.base,trace) := by
  have projected := stock_imm_projects hp ctx cfg hc (n+1) args st tr
  unfold ApplyInternal at run ⊢
  rw [run] at projected
  change .ok (some out,next.base,trace) =
    (applyTerm p (Backend.sem ctx) cfg (n+1) 27 553 args).run (st.base,tr) at projected
  have forward := stock_div_imm_pure_helper hp ctx hc (by decide) projected.symm
  rw [run] at forward
  simp only [Except.ok.injEq,Prod.mk.injEq] at forward
  exact ⟨forward.2.1,projected.symm⟩
end Backend.Stock.Proof.ScalarDiv
