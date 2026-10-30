import FV.Backend.Proof.StockCmpNonzero32RhsValues
import FV.Backend.Proof.StockCmpNonzero32OriginalSelection
import FV.Backend.Proof.StockCmpNonzero64OriginalSelection
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual original32/64 nonzero emitters derive the mapped condition and its
full marked state; arbitrary source definitions are allowed under original scope. -/
theorem stock_select_nonzero_wide_emitter_observed {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (wide : Bool) {c fuel : Nat} (enough : 220 ≤ fuel)
    (typed : ctx.valueType? c = some (.int (if wide then 64 else 32)))
    {st middle : State} {tr trace : Array RuleId} {condition : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 123 651 [.value c] (st,tr) condition (middle,trace)) :
    DemandAllowed ctx st c ∧ ∃ key,ctx.valueReg? c = some (.vreg key .int) ∧
      condition = .data 123 1 [.reg (.vreg key .int),.data 93 (if wide then 1 else 0) []] ∧
      middle = st.mark c := by
  cases wide
  · obtain ⟨rhsTrace,rhs,_⟩ := ScalarCmp.stock_cmp_original_nonzero32_selected ctx inv (by omega) typed run
    obtain ⟨n,gas⟩ : ∃ n,fuel=n+220 := ⟨fuel-220,by omega⟩
    rw [gas] at rhs
    obtain ⟨safe,rx,mapped,output,state⟩ := ScalarCmp.stock_cmp_nonzero32_rhs_observed data_program ctx typed rhs
    obtain ⟨key,rfl⟩ := inv.valueReg c rx mapped
    exact ⟨safe,key,mapped,output,state⟩
  · obtain ⟨rhsTrace,rhs,_⟩ := ScalarCmp.stock_cmp_original_nonzero64_selected ctx inv (by omega) typed run
    obtain ⟨n,gas⟩ : ∃ n,fuel=n+30 := ⟨fuel-30,by omega⟩
    rw [gas] at rhs
    obtain ⟨safe,rx,mapped,output,state⟩ := ScalarCmp.stock_cmp_nonzero64_rhs_observed data_program ctx rfl rhs
    obtain ⟨key,rfl⟩ := inv.valueReg c rx mapped
    exact ⟨safe,key,mapped,output,state⟩
end Backend.Stock.Proof.ScalarSelect
