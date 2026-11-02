import FV.Backend.Proof.StockCmpNonzero8Emission
import FV.Backend.Proof.StockCmpNonzero8OriginalSelection
import FV.Backend.Proof.StockSelectNonzero16Shape
import FV.Backend.Proof.StockSelectNonzeroWideShape

namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000

/-- Actual nonzero condition production defines only registers allocated by
that real producer. In particular it cannot define a later proof companion's
result number, even if an original available value resolves to that number. -/
theorem stock_select_nonzero_prefix {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cty : Clif.Ty}
    (width : cty.width = 8 ∨ cty.width = 16 ∨ cty.width = 32 ∨ cty.width = 64)
    {c fuel : Nat} (enough : 220 ≤ fuel) (typed : ctx.valueType? c = some (.int cty.width))
    {before next : State} {trace final : Array RuleId} {raw : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 123 651 [.value c]
      (before,trace) raw (next,final)) :
    ∃ code,Frag before.base next.base code := by
  cases cty
  case i8 =>
    obtain ⟨_,rhs,_⟩ := ScalarCmp.stock_cmp_original_nonzero8_selected ctx inv (by omega) typed run
    obtain ⟨n,gas⟩ : ∃ n,fuel=n+100 := ⟨fuel-100,by omega⟩
    rw [gas] at rhs
    obtain ⟨_,_,_,_,finish⟩ := ScalarCmp.stock_cmp_nonzero8_rhs_observed data_program ctx rfl rhs
    exact ⟨[],by rw [finish]; exact Frag.nil _⟩
  case i16 =>
    obtain ⟨_,key,mapped,_,finish⟩ := stock_select_nonzero16_emitter_observed inv enough typed run
    rw [finish]
    refine ⟨_,Frag.fresh_emit _ ?_⟩
    simp only [LState.fresh,vdefs_extend']
    exact List.Subset.refl _
  case i32 | f32 =>
    obtain ⟨_,key,_,_,finish⟩ := stock_select_nonzero_wide_emitter_observed inv false enough typed run
    exact ⟨[],by rw [finish]; exact Frag.nil _⟩
  case i64 | f64 =>
    obtain ⟨_,key,_,_,finish⟩ := stock_select_nonzero_wide_emitter_observed inv true enough typed run
    exact ⟨[],by rw [finish]; exact Frag.nil _⟩
  case i128 => simp [Clif.Ty.width] at width

end Backend.Stock.Proof.ScalarSelect
