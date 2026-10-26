import FV.Backend.Proof.StockZeroConditionPrefix
import FV.Backend.Proof.StockOriginalConditionPrefix
import FV.Backend.Proof.StockSelectComparisonCompanionWitness
import FV.Backend.Proof.StockConditionPrefix
import FV.Backend.Proof.StockSelectConditionShapeWitness

namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Every supported scalar width has an actual condition execution inhabiting
its real fresh-definition prefix, reusing the complete original source fixture. -/
theorem stock_select_nonzero_prefix_witness (ty : Clif.Ty)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) :
    ∃ f ctx before next raw trace code,LowerScope f ∧ MappedCtxInv f ctx ∧
      ApplyInternal program (Stock.sem ctx) {} 1000 123 651 [.value 7]
        (before,#[]) raw (next,trace) ∧ Frag before.base next.base code := by
  obtain ⟨f,ctx,before,next,raw,trace,scope,inv,typed,run,_,_⟩ :=
    ConditionShapeWitness.stock_select_nonzero_condition_shape_witness ty width
  obtain ⟨code,fragment⟩ := stock_select_nonzero_prefix inv width (by decide) typed run
  exact ⟨f,ctx,before,next,raw,trace,code,scope,inv,run,fragment⟩



/-- Mirrored equality/inequality RHSs at every scalar width inhabit real prefix
composition, including the actual state-preserving condition inversion. -/
theorem stock_select_zero_prefix_witness (ty : Clif.Ty) (left nonzero : Bool)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) :
    ∃ f ctx before out next trace code,LowerScope f ∧ MappedCtxInv f ctx ∧
      (evalExpr program (Stock.sem ctx) {} 1000 (ScalarCmp.cmpZeroRule left nonzero).rhs
        #[some (.value 7)]).run (before,#[]) = .ok (some out,next,trace) ∧
      Frag before.base next.base code := by
  obtain ⟨f,ctx,before,out,next,trace,scope,inv,typed,run,_⟩ :=
    ConditionShapeWitness.stock_select_zero_rhs_shape_witness ty left nonzero width
  obtain ⟨code,fragment⟩ := stock_select_zero_rhs_prefix inv width left nonzero
    (x := 7) (y := 7) (n := 760) typed typed (by simpa only [ite_self] using run)
  exact ⟨f,ctx,before,out,next,trace,code,scope,inv,run,fragment⟩

/-- Every scalar width/comparison and all operand words inhabit the actual
comparison prefix, reusing complete original source/condition fixtures. -/
theorem stock_select_comparison_prefix_witness (ty : Clif.Ty) (cc : Clif.IntCC)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (a b : BitVec ty.width) (int : ty.isInt = true) :
    ∃ f ctx before next raw trace code,LowerScope f ∧ MappedCtxInv f ctx ∧
      ApplyInternal program (Stock.sem ctx) {} 1000 123 652
        [.data 145 (ccIdx cc) [],.value 7,.value 31] (before,#[]) raw (next,trace) ∧
      Frag before.base next.base code := by
  obtain ⟨f,ctx,before,next,raw,trace,fr,aliases,ρ,scope,inv,dfg,getA,getB,typeA,typeB,run,_,_⟩ :=
    ComparisonCompanionWitness.stock_select_comparison_companion_complete_witness ty cc width a b int
  obtain ⟨code,fragment⟩ := ConditionalValues.comparison_prefix inv width cc typeA typeB (by decide) run
  exact ⟨f,ctx,before,next,raw,trace,code,scope,inv,run,fragment⟩

end Backend.Stock.Proof.ScalarSelect
