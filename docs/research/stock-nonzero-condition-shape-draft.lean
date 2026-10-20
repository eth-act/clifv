import FV.Backend.Proof.StockSelectParameterDerivedSourceValues
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
/-- All scalar source nonzero emitters produce a decoded scalar condition.
This is the structural bridge for actual652 zero and inverse-zero branches. -/
theorem stock_select_nonzero_actual_condition_shape {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cty : Clif.Ty}
    (width : cty.width = 8 ∨ cty.width = 16 ∨ cty.width = 32 ∨ cty.width = 64)
    {c fuel : Nat} (enough : 220 ≤ fuel) (typed : ctx.valueType? c = some (.int cty.width))
    {st middle : State} {tr trace : Array RuleId} {condition : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 123 651 [.value c] (st,tr) condition (middle,trace)) :
    CondShape condition (fun _ => True) := by
  cases cty
  case i8 =>
    obtain ⟨rhsTrace,rhs,_⟩ := ScalarCmp.stock_cmp_original_nonzero8_selected ctx inv (by omega) typed run
    obtain ⟨n,gas⟩ : ∃ n,fuel=n+100 := ⟨fuel-100,by omega⟩
    rw [gas] at rhs
    obtain ⟨_,rx,mapped,producer,_⟩ := ScalarCmp.stock_cmp_nonzero8_rhs_observed data_program ctx rfl rhs
    obtain ⟨key,rfl⟩ := inv.valueReg c rx mapped
    rw [producer]
    exact Or.inr (Or.inr ⟨_,_,Cond.ne,rfl,ofV_tst .xzr (.vreg key .int) ⟨255,.size32⟩,
      by decide,by decide,rfl,fun _ _ => trivial⟩)
  case i16 =>
    obtain ⟨_,key,_,producer,_⟩ := stock_select_nonzero16_emitter_observed inv enough typed run
    rw [producer]
    exact Or.inr (Or.inl ⟨st.base.nextVreg,0,.size32,rfl,rfl,trivial⟩)
  case i32 =>
    obtain ⟨_,key,_,producer,_⟩ := stock_select_nonzero_wide_emitter_observed inv false enough typed run
    rw [producer]
    exact Or.inr (Or.inl ⟨key,0,.size32,rfl,rfl,trivial⟩)
  case i64 =>
    obtain ⟨_,key,_,producer,_⟩ := stock_select_nonzero_wide_emitter_observed inv true enough typed run
    rw [producer]
    exact Or.inr (Or.inl ⟨key,1,.size64,rfl,rfl,trivial⟩)
  case i128 => simp [Clif.Ty.width] at width
end Backend.Stock.Proof.ScalarSelect
#print axioms Backend.Stock.Proof.ScalarSelect.stock_select_nonzero_actual_condition_shape
