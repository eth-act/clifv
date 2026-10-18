import FV.Backend.Proof.StockCmpNonconstantSelection
import FV.Backend.Proof.StockDFG
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
/-- Original source definitions provide the complete constant classification;
no caller-supplied comparison-path certificate is required. -/
theorem stock_cmp_original_constant_cases {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (x : Nat) :
    NonConstantSource ctx x ∨ ∃ j,∃ info,∃ ty : Clif.Ty,∃ c : BitVec ty.width,
      ctx.defInst? x = some j ∧ ctx.insts[j]? = some info ∧
      info.clif = some (.iconst ty c) ∧
      info.data = .data 152 35 [.data 151 57 [],.int (imm64OfIconst ty c)] := by
  classical
  by_cases h : NonConstantSource ctx x
  · exact Or.inl h
  · right
    apply Classical.byContradiction
    intro absent
    apply h
    intro j info defined found ty c original
    apply absent
    have raw := inv.identityView.data j info (.iconst ty c) found original
    have valid : eTy ty = true := by
      simpa [Compile.instE,Compile.tyE,eTy] using inv.instE j info _ found original
    have encoded : instData f (.iconst ty c) =
        .ok (.data 152 35 [.data 151 57 [],.int (imm64OfIconst ty c)]) := by
      simp only [instData,valid,ite_true]
      rfl
    rw [encoded] at raw
    exact ⟨j,info,ty,c,defined,found,original,(Except.ok.inj raw).symm⟩
/-- A real built context contains both a parameter and an original constant,
inhabiting both branches of the classification. -/
theorem stock_cmp_original_constant_cases_witness :
    ∃ f ctx,MappedCtxInv f ctx ∧ NonConstantSource ctx 7 ∧
      ∃ j info,ctx.defInst? 2 = some j ∧ ctx.insts[j]? = some info ∧
        info.clif = some (.iconst .i8 (9#8)) ∧
        info.data = .data 152 35 [.data 151 57 [],.int 9] := by
  obtain ⟨_,_,inv,_⟩ := buildCtx_mappedInv_witness
  refine ⟨_,_,inv,?_,?_⟩
  · intro j info defined found ty c original
    change none = some j at defined
    cases defined
  · exact ⟨0,_,rfl,rfl,rfl,rfl⟩
end Backend.Stock.Proof.ScalarCmp
