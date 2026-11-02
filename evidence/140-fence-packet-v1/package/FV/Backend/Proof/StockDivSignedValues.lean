import FV.Backend.Proof.StockDivGeneralValues
import FV.Backend.Proof.StockDivSafeValues
import FV.Backend.Proof.StockDivSignedSelected
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
theorem stock_div_sdiv_selected_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {id x y : Nat} {ty : Clif.Ty} {info : IInfo} (source : ctx.insts[id]? = some info)
    (clif : info.clif = some (.div .sdiv ty x y))
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx id st out next rules)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {u v : BitVec ty.width}
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (idem : ∀ k,aliasNum aliases (aliasNum aliases k) = aliasNum aliases k)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k)))
    (outside : ∀ z key,ctx.valueReg? z = some (.vreg key .int) → (fr.regs z).isSome = true →
      aliasNum aliases key < st.base.nextVreg ∨ next.base.nextVreg ≤ aliasNum aliases key) :
    SourceDivisionOut F isem .sdiv ty u v st next out aliases ρ := by
  have widths := (stock_div_source_data inv .sdiv source clif).1
  have observed := stock_div_sdiv_selected inv source clif selected
  rcases observed with general | ⟨j,constant,i,defined,found,data,guard,safe⟩
  · by_cases wide : ty.width = 64
    · simp only [wide,ite_true] at general
      have original : GeneralSdivReceipt program ctx true 999899 x y ty.width st next #[] out := by
        simpa only [wide] using general
      exact stock_div_general_sdiv_values (ty := ty) inv true wide source clif original refines dfg getX getY bounded idem extent held outside
    · simp only [wide,ite_false] at general
      exact stock_div_general_sdiv_values (ty := ty) inv false (by simp only [Bool.false_eq_true,ite_false]; omega) source clif general refines dfg getX getY bounded idem extent held outside
  · have relation : if (ty.width == 64) then ty.width = 64 else ty.width ≤ 32 := by
      by_cases wide : ty.width = 64 <;> simp [wide] <;> omega
    exact stock_div_safe_sdiv_values inv (ty.width == 64) relation source clif defined found data guard safe
      refines dfg getX getY bounded idem extent held outside
end Backend.Stock.Proof.ScalarDiv
