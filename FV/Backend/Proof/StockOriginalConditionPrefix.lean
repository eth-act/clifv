import FV.Backend.Proof.StockComparisonPrefixWide
import FV.Backend.Proof.StockComparisonPrefixNarrow
import FV.Backend.Proof.StockConditionPrefix
import FV.Backend.Proof.StockSelectConditionOriginValues

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open ScalarSelect
set_option autoImplicit false

/-- Every supported comparison emitter's real prefix defines only registers
allocated before its actual endpoint. All operand forms reuse existing observed
execution facts; no restriction on final source aliases is introduced. -/
theorem comparison_prefix {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {ty : Clif.Ty}
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) (cc : Clif.IntCC)
    {x y fuel : Nat} (typeX : ctx.valueType? x = some (.int ty.width))
    (typeY : ctx.valueType? y = some (.int ty.width)) (enough : 300 ≤ fuel)
    {before next : State} {trace final : Array RuleId} {raw : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 123 652
      [.data 145 (ccIdx cc) [],.value x,.value y] (before,trace) raw (next,final)) :
    ∃ code,Frag before.base next.base code := by
  cases ty
  case i8 => exact stock_select_narrow_comparison_prefix inv cc false typeX typeY enough run
  case i16 => exact stock_select_narrow_comparison_prefix inv cc true typeX typeY enough run
  case i32 | f32 => exact stock_select_wide_comparison_prefix inv cc false typeX typeY enough run
  case i64 | f64 => exact stock_select_wide_comparison_prefix inv cc true typeX typeY enough run
  case i128 => simp [Clif.Ty.width] at width

/-- Original650 derives its real fresh-only prefix from source condition
provenance and original DFG/typing. A later companion destination is outside its
definitions even when an available source value resolves to that number. -/
theorem original_prefix {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cty : Clif.Ty} {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {c : Nat} {test : BitVec cty.width} (getC : fr.getAs c cty = .ok test)
    (typedReads : ∀ {value : Nat} {ty : Clif.Ty} {bits : BitVec ty.width},
      fr.getAs value ty = .ok bits → ctx.valueType? value = some (.int ty.width))
    {fuel : Nat} (enough : 400 ≤ fuel) {before next : State}
    {trace final : Array RuleId} {raw : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 123 650 [.value c]
      (before,trace) raw (next,final)) :
    ∃ code,Frag before.base next.base code := by
  have supported : ∀ {value : Nat} {ty : Clif.Ty} {bits : BitVec ty.width},
      fr.getAs value ty = .ok bits →
      ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64 := by
    intro value ty bits read
    have valid := inv.valTyE value (.int ty.width) (typedReads read)
    cases ty <;> simp [eCTys,Clif.Ty.width] at valid ⊢
  rcases stock_original_select_condition_calls inv enough run with
    ⟨helperFuel,helperTrace,enoughHelper,nonzero⟩ |
    ⟨cc,ty,a,b,origin,helperFuel,helperTrace,enoughHelper,comparison⟩
  · exact stock_select_nonzero_prefix inv (supported getC) (by omega) (typedReads getC) nonzero
  · obtain ⟨av,bv,getA,getB,_⟩ := stock_select_comparison_origin_values dfg origin (getAs_ok getC)
    exact comparison_prefix inv (supported getA) cc (typedReads getA) (typedReads getB) enoughHelper comparison

end Backend.Stock.Proof.ConditionalValues
