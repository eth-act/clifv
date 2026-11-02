import FV.Backend.Proof.StockCmpNonzeroNarrowCalls
import FV.Backend.Proof.StockCmpNonzero16OriginalSelection
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- The original16-bit condition emitter derives its real scratch extension
and its complete guarded scheduling state. -/
theorem stock_select_nonzero16_emitter_observed {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {c fuel : Nat} (enough : 220 ≤ fuel)
    (typed : ctx.valueType? c = some (.int 16))
    {st middle : State} {tr trace : Array RuleId} {condition : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 123 651 [.value c] (st,tr) condition (middle,trace)) :
    DemandAllowed ctx st c ∧ ∃ key,ctx.valueReg? c = some (.vreg key .int) ∧
      condition = .data 123 1 [.reg (st.base.fresh .int).1,.data 93 0 []] ∧
      middle = {st.mark c with base := (st.base.fresh .int).2.emit (.extend (st.base.fresh .int).1 (.vreg key .int) false 16 32)} := by
  obtain ⟨rhsTrace,rhs,_⟩ := ScalarCmp.stock_cmp_original_nonzero16_selected ctx inv (by omega) typed run
  obtain ⟨n,gas⟩ : ∃ n,fuel=n+220 := ⟨fuel-220,by omega⟩
  rw [gas] at rhs
  obtain ⟨extFuel,value,enoughExt,extension,producer⟩ := ScalarCmp.stock_cmp_nonzero_narrow_rhs_calls data_program ctx c (.int 16) n rhs
  obtain ⟨t,type,safe,rx,mapped,form⟩ := ScalarShift.stock_zext32_out data_program rfl enoughExt extension
  rw [typed] at type
  cases type
  obtain ⟨key,rfl⟩ := inv.valueReg c rx mapped
  rcases form with ⟨passes,_,_⟩ | ⟨_,_,output,finish⟩
  · simp at passes
  · rw [output] at producer
    exact ⟨safe,key,mapped,producer,finish⟩
end Backend.Stock.Proof.ScalarSelect
