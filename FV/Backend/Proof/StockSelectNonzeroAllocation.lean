import FV.Backend.Proof.StockCmpNonzero8Emission
import FV.Backend.Proof.StockCmpNonzero8OriginalSelection
import FV.Backend.Proof.StockSelectNonzero16Shape
import FV.Backend.Proof.StockSelectDecodedObserved
import FV.Backend.Proof.StockSelectZeroObserved
import FV.Backend.Proof.StockSelectNonzeroWideShape
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
/-- Actual scalar condition/select allocation is derived before value semantics,
so retained availability can establish scratch separation without circularity. -/
theorem stock_select_nonzero_actual_allocation {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cty ty : Clif.Ty}
    (conditionWidth : cty.width = 8 ∨ cty.width = 16 ∨ cty.width = 32 ∨ cty.width = 64)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    {c x y emitFuel selectFuel : Nat} (typed : ctx.valueType? c = some (.int cty.width))
    (enoughEmit : 220 ≤ emitFuel) (enoughSelect : 319 ≤ selectFuel)
    {st middle next : State} {tr emitterTrace trace : Array RuleId} {condition out : V}
    (emitter : ApplyInternal program (Stock.sem ctx) {} emitFuel 123 651 [.value c]
      (st,tr) condition (middle,emitterTrace))
    {consumerStart : Array RuleId}
    (consumer : ApplyInternal program (Stock.sem ctx) {} selectFuel 22 659
      [.ty (.int ty.width),condition,.value x,.value y] (middle,consumerStart) out (next,trace)) :
    out = .regs [.vreg middle.base.nextVreg .int] ∧ st.base.nextVreg ≤ middle.base.nextVreg ∧
      next.base.nextVreg = st.base.nextVreg+(if cty = .i16 then 2 else 1) ∧
      next.base.nextVreg = middle.base.nextVreg+1 := by
  cases cty
  case i8 =>
    obtain ⟨rhsTrace,rhs,_⟩ := ScalarCmp.stock_cmp_original_nonzero8_selected ctx inv (by omega) typed emitter
    obtain ⟨n,gas⟩ : ∃ n,emitFuel=n+100 := ⟨emitFuel-100,by omega⟩
    rw [gas] at rhs
    obtain ⟨_,rx,_,producer,finish⟩ := ScalarCmp.stock_cmp_nonzero8_rhs_observed data_program ctx rfl rhs
    rw [producer] at consumer
    obtain ⟨_,_,_,_,_,_,_,_,output,complete⟩ := stock_select_flags_decoded_observed data_program ctx rfl
      (by omega) width .ne consumer
    refine ⟨output,?_,?_,?_⟩
    · rw [finish]; exact Nat.le_refl _
    · rw [complete,finish]; rfl
    · rw [complete]; rfl
  case i16 =>
    obtain ⟨_,_,_,producer,finish⟩ := stock_select_nonzero16_emitter_observed inv enoughEmit typed emitter
    rw [producer] at consumer
    obtain ⟨_,_,_,_,_,_,output,complete⟩ := stock_select_zero_observed data_program ctx rfl enoughSelect width
      true .size32 st.base.nextVreg consumer
    refine ⟨output,?_,?_,?_⟩
    · rw [finish]; simp [LState.fresh,LState.emit]
    · rw [complete,finish]; rfl
    · rw [complete]; rfl
  case i32 | f32 =>
    obtain ⟨_,key,_,producer,finish⟩ := stock_select_nonzero_wide_emitter_observed inv false enoughEmit typed emitter
    rw [producer] at consumer
    obtain ⟨_,_,_,_,_,_,output,complete⟩ := stock_select_zero_observed data_program ctx rfl enoughSelect width
      true .size32 key consumer
    refine ⟨output,?_,?_,?_⟩
    · rw [finish]; exact Nat.le_refl _
    · rw [complete,finish]; rfl
    · rw [complete]; rfl
  case i64 | f64 =>
    obtain ⟨_,key,_,producer,finish⟩ := stock_select_nonzero_wide_emitter_observed inv true enoughEmit typed emitter
    rw [producer] at consumer
    obtain ⟨_,_,_,_,_,_,output,complete⟩ := stock_select_zero_observed data_program ctx rfl enoughSelect width
      true .size64 key consumer
    refine ⟨output,?_,?_,?_⟩
    · rw [finish]; exact Nat.le_refl _
    · rw [complete,finish]; rfl
    · rw [complete]; rfl
  case i128 => simp [Clif.Ty.width] at conditionWidth
end Backend.Stock.Proof.ScalarSelect
