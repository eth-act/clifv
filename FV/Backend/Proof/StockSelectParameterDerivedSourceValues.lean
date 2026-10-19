import FV.Backend.Proof.StockAvailableTypes
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open MinMaxRegisterFixture Backend.Stock.Proof.ScalarCmp
/-- The original condition getter, availability and restricted DFG derive both
context typing and supported condition width internally. Earlier explicit-type
source theorems remain available unchanged; no new input condition is added. -/
theorem stock_lower_select_parameter_source_values_derived_types {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {cty ty : Clif.Ty} {c x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.select ty c x y))
    (parameter : event.ctx.defInst? c = none)
    (results : info.results = [z]) (statementResults : stmt.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV} {test : BitVec cty.width} {u v : BitVec ty.width}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (getC : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs c cty = .ok test)
    (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    (getY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v)
    (held : ValuesHeld (fun value => Demanded record.output.state value ∧ value ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun key => ρ (aliasNum result.final.alias key)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ d,step.results = [[.vreg d .int]] ∧ record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg ∧
      cm' = cm ∧
      ∀ world,Runs F isem (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨ty,Clif.Sem.select test u v⟩ (ρ' d) ∧ (∀ k,k < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ k → ρ' k = ρ k) ∧
          ValuesHeld (fun value => Demanded record.input value ∧ value ∈ availOf f (availIn f result.ctx) bi (j+1))
            event.ctx fr' (fun key => ρ' (aliasNum result.final.alias key))) := by
  have availableC := restrict_regs_isSome (by rw [getAs_ok getC]; rfl)
  have typed := stock_lower_available_getAs_type run events availableC dfg getC
  have inv := (stock_lower_record_context run scope events).1
  have supported := inv.valTyE c (.int cty.width) typed
  have conditionWidth : cty.width = 8 ∨ cty.width = 16 ∨ cty.width = 32 ∨ cty.width = 64 := by
    cases cty <;> simp [eCTys,Clif.Ty.width] at supported ⊢
  exact stock_lower_select_parameter_source_values run scope dominated events records foundBlock foundStmt current
    source clif conditionWidth typed parameter results statementResults mapped recorded emitted refines dfg getC getX getY held sourceStep
end Backend.Stock.Proof.ScalarSelect
