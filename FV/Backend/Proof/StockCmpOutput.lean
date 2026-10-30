import FV.Backend.Proof.IselCmpInv
import FV.Backend.Proof.IselTerms
import FV.Backend.Proof.StockCmpPure
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- The real comparison output wrapper preserves complete Stock state while
turning its actual result register into the one-result output vector. -/
theorem stock_cmp_output_run {p : Program} (hp : Data p) (ctx : Ctx) (st : State)
    (tr : Array RuleId) (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+10) 25 172 [.reg r]).run (st,tr) =
      .ok (some (.regsVec [[r]]),st,tr.push rule_prelude_lower_105.id) := by
  exact stock_cmp_pure_helper hp ctx rfl (by decide) (output_reg_run hp ctx rfl st.base tr n r)
/-- Successful actual output wrapping supplies the complete unchanged state
and exact output internally; no independent output certificate is required. -/
theorem stock_cmp_output_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {fuel : Nat} (enough : 9 ≤ fuel) {st next : State} {tr trace : Array RuleId} {r : Reg} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) {} fuel 25 172 [.reg r] (st,tr) out (next,trace)) :
    out = .regsVec [[r]] ∧ next = st := by
  obtain ⟨n,equal⟩ : ∃ n,fuel+1=n+10 := ⟨fuel-9,by omega⟩
  unfold ApplyInternal at run
  rw [equal,stock_cmp_output_run hp ctx st tr n r] at run
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at run
  exact ⟨run.1.symm,run.2.1.symm⟩
/-- A real output wrapper with a sparse register number inhabits both execution
and successful output/state observation. -/
theorem stock_cmp_output_witness :
    ∃ trace,ApplyInternal program (Stock.sem sinkCtx) {} 999 25 172 [.reg (.vreg 100 .int)]
      (sinkState,#[]) (.regsVec [[.vreg 100 .int]]) (sinkState,trace) := by
  exact ⟨_,stock_cmp_output_run data_program sinkCtx sinkState #[] 990 (.vreg 100 .int)⟩
end Backend.Stock.Proof.ScalarCmp
