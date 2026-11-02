import FV.Backend.Proof.StockMinMaxWideCalls
import FV.Backend.Proof.StockMinMaxNarrowValues
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open MinMaxRegisterFixture Backend.Stock.Proof.ScalarCmp
/-- Universal8/16 minmax source selection composes all actual emitter forms
with real659/output execution. The retained caller derives the empty buffer and final-source
separation from original availability; no source classification is assumed. -/
theorem stock_minmax_narrow_selected_source_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (unsigned maximum half : Bool) {ty : Clif.Ty}
    (sourceTy : ty = if half then .i16 else .i8) {i x y : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (minmaxOperation unsigned maximum) ty x y))
    (typeX : ctx.valueType? x = some (.int (if half then 16 else 8)))
    (typeY : ctx.valueType? y = some (.int (if half then 16 else 8)))
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    {fr : Clif.Frame} {u v : BitVec ty.width} (dfg : DFGCons ctx fr)
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key)))
    (empty : st.base.emitted = #[])
    (outsideX : ∀ r,ctx.valueReg? x = some (.vreg r .int) →
      aliasNum aliases r < st.base.nextVreg ∨ st.base.nextVreg+2 ≤ aliasNum aliases r)
    (outsideY : ∀ r,ctx.valueReg? y = some (.vreg r .int) →
      aliasNum aliases r < st.base.nextVreg ∨ st.base.nextVreg+2 ≤ aliasNum aliases r) :
    ∃ d code,out = .regsVec [[.vreg d .int]] ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base code ∧
      ∀ world,Runs F isem (code.map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun final _ =>
          VHolds ⟨ty,Clif.Sem.binary (minmaxOperation unsigned maximum) u v⟩ (final d) ∧
          ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → final k = ρ k) := by
  obtain ⟨_,_,_,_,emitFuel,selectFuel,condition,middle,emitTrace,value,produced,selectTrace,
    enoughEmit,enoughSelect,emitter,consumer,output⟩ := stock_minmax_wide_selected_calls inv unsigned maximum source clif selected
  have outputDemand := stock_ctor_demand_mono output
  have consumerHeld : ValuesHeld (Demanded produced) ctx fr (fun key => ρ (aliasNum aliases key)) := by
    apply held.mono
    intro z needed
    have grows := outputDemand z
    unfold Demanded at needed ⊢
    omega
  obtain ⟨nx,ny,d,code,mapX,mapY,valueEq,resultEq,allocation,fragment,execution⟩ := stock_minmax_narrow_emitter_source_values
    inv unsigned maximum half sourceTy dfg getX getY typeX typeY enoughEmit enoughSelect emitter consumer
    refines bounded extent consumerHeld empty outsideX outsideY
  rw [valueEq,stock_ctor_baseOnly ctx T.output _ produced (by decide)] at output
  change ExtResult.ok (.regsVec [[.vreg d .int]],produced) = .ok (out,next) at output
  have both := Prod.mk.inj (ExtResult.ok.inj output)
  rw [← both.2]
  refine ⟨d,code,both.1.symm,(by omega),(by omega),fragment,?_⟩
  intro world
  exact (execution world).imp (fun regs _ _ post => ⟨post.1,fun k outside => post.2 k (by omega)⟩)
end Backend.Stock.Proof.ScalarSelect
