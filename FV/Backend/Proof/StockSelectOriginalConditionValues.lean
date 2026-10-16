import FV.Backend.Proof.StockSelectComparisonValues
import FV.Backend.Proof.StockSelectConditionOriginValues
import FV.Backend.Proof.StockSelectNonzeroConditionShape
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private theorem supported_read {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {value : Nat} {ty : Clif.Ty} (typed : ctx.valueType? value = some (.int ty.width)) :
    ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64 := by
  have supported := inv.valTyE value (.int ty.width) typed
  cases ty <;> simp [eCTys,Clif.Ty.width] at supported ⊢
/-- Original650 and actual659 compute the source select for every ordinary
condition definition and direct/zero-extended comparison look-through. Original
retained callers derive the source typing and separation callbacks internally. -/
theorem stock_original_select_condition_source_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cty ty : Clif.Ty}
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {c x y : Nat} {test : BitVec cty.width} {u v : BitVec ty.width}
    (getC : fr.getAs c cty = .ok test) (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    (typedReads : ∀ {value : Nat} {sourceTy : Clif.Ty} {bits : BitVec sourceTy.width},
      fr.getAs value sourceTy = .ok bits → ctx.valueType? value = some (.int sourceTy.width))
    {emitFuel selectFuel : Nat} (enoughEmit : 400 ≤ emitFuel) (enoughSelect : 319 ≤ selectFuel)
    {st middle next : State} {tr emitTrace consumerStart trace : Array RuleId} {raw out : V}
    (empty : st.base.emitted = #[])
    (emitter : ApplyInternal program (Stock.sem ctx) {} emitFuel 123 650 [.value c] (st,tr) raw (middle,emitTrace))
    (consumer : ApplyInternal program (Stock.sem ctx) {} selectFuel 22 659
      [.ty (.int ty.width),raw,.value x,.value y] (middle,consumerStart) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key)))
    (outsideReads : ∀ {value : Nat} {sourceTy : Clif.Ty} {bits : BitVec sourceTy.width},
      fr.getAs value sourceTy = .ok bits → ∀ key,ctx.valueReg? value = some (.vreg key .int) →
        aliasNum aliases key < st.base.nextVreg ∨ next.base.nextVreg ≤ aliasNum aliases key) :
    ∃ d code,out = .regs [.vreg d .int] ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base code ∧
      ∀ world,Runs F isem (code.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world
        (fun final _ => VHolds ⟨ty,Clif.Sem.select test u v⟩ (final d) ∧
          ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → final k = ρ k) := by
  rcases stock_original_select_condition_calls inv enoughEmit emitter with
    ⟨helperFuel,helperTrace,enough,nonzero⟩ | ⟨cc,compareTy,a,b,origin,helperFuel,helperTrace,enough,comparison⟩
  · exact stock_select_nonzero_actual_source_values inv (supported_read inv (typedReads getC)) width dfg
      getC getX getY (typedReads getC) (by omega) enoughSelect empty nonzero consumer refines bounded extent held
      (outsideReads getX) (outsideReads getY)
  · obtain ⟨av,bv,getA,getB,truth⟩ := stock_select_comparison_origin_values dfg origin (getAs_ok getC)
    have typeA := typedReads getA
    have typeB := typedReads getB
    have comparisonWidth := supported_read inv typeA
    have shape := stock_select_comparison_condition_shape inv comparisonWidth cc typeA typeB enough comparison
    obtain ⟨_,actualProducer,condition,rx,ry,_,_,_,_,_,_,_,finish⟩ :=
      stock_select_decoded_condition_observed ctx shape width enoughSelect consumer
    have monotone := (stock_apply_allocationLe comparison).1
    have frontier : next.base.nextVreg = middle.base.nextVreg+1 := by rw [finish]; rfl
    have separatedB : ∀ key,ctx.valueReg? b = some (.vreg key .int) → aliasNum aliases key ≠ st.base.nextVreg := by
      intro key mapped equal
      have outside := outsideReads getB key mapped
      omega
    obtain ⟨d,code,output,lower,upper,fragment,runs⟩ := stock_select_comparison_actual_source_values inv comparisonWidth width cc dfg
      getA getB getX getY typeA typeB enough enoughSelect empty comparison consumer refines bounded extent held
      separatedB (outsideReads getX) (outsideReads getY)
    exact ⟨d,code,output,lower,upper,fragment,by simpa only [Clif.Sem.select,truth] using runs⟩
end Backend.Stock.Proof.ScalarSelect
