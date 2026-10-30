import FV.Backend.Proof.StockSelectComparisonValues
import FV.Backend.Proof.StockSelectConditionSuccess
import FV.Backend.Proof.StockSelectComparisonActualFixture
namespace Backend.Stock.Proof.ScalarSelect.ComparisonActualWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Every original scalar width/comparison condition and every source operand
pair inhabits actual652→659 execution and the complete source value/frame result,
with dirty high bits and nonidentity aliases supplied by the original fixture.

Compatibility boundary (S11b, #140): original integer domain only; `int` is a trailing
auto-parameter (`decide`) so the original call shapes are unchanged. -/
theorem stock_select_comparison_actual_complete_witness (ty : Clif.Ty) (cc : Clif.IntCC)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) (a b : BitVec ty.width)
    (int : ty.isInt = true := by decide) :
    ∃ f ctx st middle next raw out emitTrace trace fr aliases,∃ (ρ : Nat → CV),
      LowerScope f ∧ MappedCtxInv f ctx ∧ DFGCons ctx fr ∧
      fr.getAs 7 ty = .ok a ∧ fr.getAs 31 ty = .ok b ∧
      ctx.valueType? 7 = some (.int ty.width) ∧ ctx.valueType? 31 = some (.int ty.width) ∧
      CondShape raw (fun _ => True) ∧
      ApplyInternal program (Stock.sem ctx) {} 1000 123 652
        [.data 145 (ccIdx cc) [],.value 7,.value 31] (st,#[]) raw (middle,emitTrace) ∧
      ApplyInternal program (Stock.sem ctx) {} 999 22 659
        [.ty (.int ty.width),raw,.value 7,.value 31] (middle,emitTrace) out (next,trace) ∧
      ∃ d code,out = .regs [.vreg d .int] ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
        Frag st.base next.base code ∧
        ∀ world,Runs (fun _ => True) ispec (code.map
          (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world
          (fun final _ => VHolds ⟨ty,if Clif.Sem.intcc cc a b then a else b⟩ (final d) ∧
            ∀ key,key < st.base.nextVreg ∨ next.base.nextVreg ≤ key → final key = ρ key) := by
  obtain ⟨f,ctx,st,middle,raw,emitTrace,fr,aliases,ρ,scope,inv,dfg,getA,getB,typeA,typeB,
    mapA,mapB,aliasA,aliasB,start,empty,bounded,extent,held,guards,emitter⟩ :=
    ComparisonActualFixture.stock_select_comparison_actual_fixture ty cc width a b int
  have shape := stock_select_comparison_condition_shape inv width cc typeA typeB (by decide) emitter
  obtain ⟨out,next,trace,consumer⟩ := stock_select_decoded_condition_success ctx shape width middle emitTrace
    mapA mapB (guards middle).1 (guards (middle.mark 7)).2
  have separateB : ∀ key,ctx.valueReg? 31 = some (.vreg key .int) → aliasNum aliases key ≠ st.base.nextVreg := by
    intro key mapped
    have keyEq := (Reg.vreg.inj (Option.some.inj (mapped.symm.trans mapB))).1
    subst key
    rw [aliasB,start]
    decide
  have outsideA : ∀ key,ctx.valueReg? 7 = some (.vreg key .int) →
      aliasNum aliases key < st.base.nextVreg ∨ next.base.nextVreg ≤ aliasNum aliases key := by
    intro key mapped
    have keyEq := (Reg.vreg.inj (Option.some.inj (mapped.symm.trans mapA))).1
    subst key
    rw [aliasA,start]
    exact Or.inl (by decide)
  have outsideB : ∀ key,ctx.valueReg? 31 = some (.vreg key .int) →
      aliasNum aliases key < st.base.nextVreg ∨ next.base.nextVreg ≤ aliasNum aliases key := by
    intro key mapped
    have keyEq := (Reg.vreg.inj (Option.some.inj (mapped.symm.trans mapB))).1
    subst key
    rw [aliasB,start]
    exact Or.inl (by decide)
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ world _ h => ⟨world,h,SameWorld.refl _ _⟩
  exact ⟨f,ctx,st,middle,next,raw,out,emitTrace,trace,fr,aliases,ρ,scope,inv,dfg,getA,getB,typeA,typeB,shape,
    emitter,consumer,stock_select_comparison_actual_source_values inv width width cc dfg getA getB getA getB
      typeA typeB (by decide) (by decide) empty emitter consumer self bounded extent (held next) separateB outsideA outsideB⟩
end Backend.Stock.Proof.ScalarSelect.ComparisonActualWitness
