module

public import FV.Backend.Proof.StockSelectOriginalConditionValues
public import FV.Backend.Proof.StockSelectOriginalSourceMatch

@[expose] public section

namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private theorem output_state {ctx : Ctx} {value out : V} {st next : State}
    (run : Stock.externCtor ctx T.output [value] st = .ok (out,next)) : next = st := by
  rw [stock_ctor_baseOnly ctx T.output _ st (by decide)] at run
  cases value <;> cases run <;> rfl
/-- Actual selected original select at the original unique root computes the
original chosen value and full fresh-write frame. Its retained caller derives
source separation from original availability before invoking this theorem. -/
theorem stock_original_select_selected_source_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cty ty : Clif.Ty}
    {i c x y : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.select ty c x y))
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {test : BitVec cty.width} {u v : BitVec ty.width}
    (getC : fr.getAs c cty = .ok test) (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    (typedReads : ∀ {value : Nat} {sourceTy : Clif.Ty} {bits : BitVec sourceTy.width},
      fr.getAs value sourceTy = .ok bits → ctx.valueType? value = some (.int sourceTy.width))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key)))
    (empty : st.base.emitted = #[])
    (outsideReads : ∀ {value : Nat} {sourceTy : Clif.Ty} {bits : BitVec sourceTy.width},
      fr.getAs value sourceTy = .ok bits → ∀ key,ctx.valueReg? value = some (.vreg key .int) →
        aliasNum aliases key < st.base.nextVreg ∨ next.base.nextVreg ≤ aliasNum aliases key) :
    ∃ d code,out = .regsVec [[.vreg d .int]] ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base code ∧
      ∀ world,Runs F isem (code.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world
        (fun final _ => VHolds ⟨ty,Clif.Sem.select test u v⟩ (final d) ∧
          ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → final k = ρ k) := by
  obtain ⟨_,_,_,_,emitFuel,selectFuel,condition,middle,emitTrace,value,produced,selectTrace,
    enoughEmit,enoughSelect,emitter,consumer,output⟩ := stock_original_select_selected_calls inv source clif selected
  have sameState : next = produced := output_state output
  rw [sameState] at held outsideReads ⊢
  obtain ⟨d,code,actualOutput,lower,upper,fragment,execution⟩ := stock_original_select_condition_source_values inv
    (stock_original_select_source_data inv source clif).1 dfg getC getX getY typedReads enoughEmit enoughSelect
    empty emitter consumer refines bounded extent held outsideReads
  rw [actualOutput,stock_ctor_baseOnly ctx T.output _ produced (by decide)] at output
  change ExtResult.ok (.regsVec [[.vreg d .int]],produced) = .ok (out,next) at output
  have both := Prod.mk.inj (ExtResult.ok.inj output)
  exact ⟨d,code,both.1.symm,lower,upper,fragment,execution⟩
end Backend.Stock.Proof.ScalarSelect
