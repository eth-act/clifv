import FV.Backend.Proof.StockConditionalBranchValues
import FV.Backend.Proof.StockConditionalCalls
import FV.Backend.Proof.StockDemandMono

namespace Backend.Stock.Proof.ConditionalCalls
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open ConditionalValues
set_option autoImplicit false
set_option Elab.async false

/-- The actual selected call packet establishes source branch execution from
values held at its output state. Demand monotonicity derives the intermediate
condition contract internally, without exposing a helper-state premise. -/
theorem Calls.source_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    {cty : Clif.Ty} {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {test : BitVec cty.width} (getC : fr.getAs c cty = .ok test)
    (typedReads : ∀ {value : Nat} {ty : Clif.Ty} {bits : BitVec ty.width},
      fr.getAs value ty = .ok bits → ctx.valueType? value = some (.int ty.width))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ before.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < before.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key)))
    (separatedReads : ∀ {value : Nat} {ty : Clif.Ty} {bits : BitVec ty.width},
      fr.getAs value ty = .ok bits → ∀ key,ctx.valueReg? value = some (.vreg key .int) →
        aliasNum aliases key ≠ before.base.nextVreg) :
    ∃ yes no code,labels = [yes,no] ∧ Frag before.base next.base code ∧
      ∀ world,BranchExecution F isem yes no (code.map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))))
        (test != 0) before.base next.base ρ world := by
  have constructMono := stock_apply_demand_mono calls.constructRun
  have emitMono := stock_apply_demand_mono calls.emitRun
  have intermediate : ValuesHeld (Demanded calls.middle) ctx fr
      (fun key => ρ (aliasNum aliases key)) := held.mono (by
    intro value needed
    have first := constructMono value
    have second := emitMono value
    unfold Demanded at needed ⊢
    omega)
  have conditionRun := calls.conditionRun
  rw [source] at conditionRun
  obtain ⟨code,fragment,execution⟩ := original_source_branch_values inv dfg getC typedReads
    calls.conditionEnough calls.constructEnough calls.emitEnough conditionRun
    calls.constructRun calls.emitRun refines bounded extent intermediate separatedReads
  exact ⟨calls.yes,calls.no,code,calls.labels_eq,fragment,execution⟩


/-- Parameter branches derive actual selected source execution from final
branch demand with no scratch or companion-register inequality. -/
theorem Calls.parameter_source_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i : Nat} {labels : List Label}
    {before next : State} {out : V} (calls : Calls ctx i labels before out next)
    {c : Nat} (source : calls.source = .value c)
    {cty : Clif.Ty} {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {test : BitVec cty.width} (getC : fr.getAs c cty = .ok test)
    (typed : ctx.valueType? c = some (.int cty.width))
    (parameter : ctx.defInst? c = none)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ before.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < before.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ yes no code,labels = [yes,no] ∧ Frag before.base next.base code ∧
      ∀ world,BranchExecution F isem yes no (code.map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))))
        (test != 0) before.base next.base ρ world := by
  have constructMono := stock_apply_demand_mono calls.constructRun
  have emitMono := stock_apply_demand_mono calls.emitRun
  have intermediate : ValuesHeld (Demanded calls.middle) ctx fr
      (fun key => ρ (aliasNum aliases key)) := held.mono (by
    intro value needed
    have first := constructMono value
    have second := emitMono value
    unfold Demanded at needed ⊢
    omega)
  have conditionRun := calls.conditionRun
  rw [source] at conditionRun
  obtain ⟨code,fragment,execution⟩ := parameter_source_branch_values inv dfg getC typed parameter
    calls.conditionEnough calls.constructEnough calls.emitEnough conditionRun
    calls.constructRun calls.emitRun refines bounded extent intermediate
  exact ⟨calls.yes,calls.no,code,calls.labels_eq,fragment,execution⟩

end Backend.Stock.Proof.ConditionalCalls
