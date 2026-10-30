import FV.Backend.Proof.IselCmpMinMax
import FV.Backend.Proof.StockMinMaxSelectedCalls
import FV.Backend.Proof.StockMinMaxNonconstantValues
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open MinMaxRegisterFixture Backend.Stock.Proof.ScalarCmp
/-- The actual original min/max root and652 emitter selection compose through
659 and output into the original32/64 min/max value. Nonconstant operands are
an internal source case; constant/narrow cases must still join the full dispatch. -/
theorem stock_minmax_register_selected_source_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (unsigned maximum : Bool) {ty : Clif.Ty}
    (width : ty.width = 32 ∨ ty.width = 64) {i x y : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (minmaxOperation unsigned maximum) ty x y))
    (typeX : ctx.valueType? x = some (.int (szOf ty.width).bits))
    (typeY : ctx.valueType? y = some (.int (szOf ty.width).bits))
    (notConstantX : NonConstantSource ctx x) (notConstantY : NonConstantSource ctx y)
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    {fr : Clif.Frame} {u v : BitVec ty.width} (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ d code,out = .regsVec [[.vreg d .int]] ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base code ∧
      ∀ world,Runs F isem (code.map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨ty,Clif.Sem.binary (minmaxOperation unsigned maximum) u v⟩ (ρ' d) ∧
          ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k) := by
  obtain ⟨_,_,_,_,calls⟩ := stock_minmax_selected_calls inv unsigned maximum source clif selected
  obtain ⟨emitFuel,selectFuel,condition,middle,emitTrace,value,produced,selectTrace,
    enoughEmit,enoughSelect,emitter,consumer,output⟩ := calls
  have outputDemand := stock_ctor_demand_mono output
  have consumerHeld : ValuesHeld (Demanded produced) ctx fr (fun key => ρ (aliasNum aliases key)) := by
    apply held.mono
    intro z needed
    have grows := outputDemand z
    unfold Demanded at needed ⊢
    omega
  obtain ⟨nx,ny,d,mapX,mapY,valueEq,lower,upper,fragment,execution⟩ := stock_minmax_nonconstant_emitter_source_values
    data_program inv (minmaxComparison unsigned maximum) width getX getY typeX typeY notConstantX notConstantY
    enoughEmit enoughSelect emitter consumer refines bounded extent consumerHeld
  rw [valueEq,stock_ctor_baseOnly ctx T.output _ produced (by decide)] at output
  change ExtResult.ok (.regsVec [[.vreg d .int]],produced) = .ok (out,next) at output
  have both := Prod.mk.inj (ExtResult.ok.inj output)
  have semantics : (if Clif.Sem.intcc (minmaxComparison unsigned maximum) u v then u else v) =
      Clif.Sem.binary (minmaxOperation unsigned maximum) u v := by
    cases unsigned <;> cases maximum
    · exact (minmax_sem ty.width u v).2.1
    · exact (minmax_sem ty.width u v).2.2.2
    · exact (minmax_sem ty.width u v).1
    · exact (minmax_sem ty.width u v).2.2.1
  rw [← both.2]
  refine ⟨d,_,both.1.symm,lower,upper,fragment,?_⟩
  intro world
  apply (execution world).imp
  intro ρ' _ _ result
  refine ⟨?_,?_⟩
  · have heldValue := result.1
    change (ρ' d).setWidth ty.width = _ at heldValue ⊢
    exact heldValue.trans semantics
  · intro k outside
    exact result.2 k (by omega)
end Backend.Stock.Proof.ScalarSelect
