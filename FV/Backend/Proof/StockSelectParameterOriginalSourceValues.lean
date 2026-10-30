import FV.Backend.Proof.StockSelectParameterRecordValues
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open MinMaxRegisterFixture Backend.Stock.Proof.ScalarCmp
/-- Original retained select with a parameter condition transfers values to the
actual original source-step frame and preserves memory and the guarded post-frame. -/
theorem stock_lower_select_parameter_source_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {cty ty : Clif.Ty} {c x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.select ty c x y))
    (conditionWidth : cty.width = 8 ∨ cty.width = 16 ∨ cty.width = 32 ∨ cty.width = 64)
    (typed : event.ctx.valueType? c = some (.int cty.width)) (parameter : event.ctx.defInst? c = none)
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
  have rawGetC : fr.getAs c cty = .ok test :=
    (getAs_congr (fr := restrict fr (availOf f (availIn f result.ctx) bi j)) (fr' := fr)
      (x := c) (ty := cty) (restrict_regs_of_mem availableC).symm).trans getC
  have availableX := restrict_regs_isSome (by rw [getAs_ok getX]; rfl)
  have availableY := restrict_regs_isSome (by rw [getAs_ok getY]; rfl)
  have rawGetX : fr.getAs x ty = .ok u :=
    (getAs_congr (fr := restrict fr (availOf f (availIn f result.ctx) bi j)) (fr' := fr)
      (x := x) (ty := ty) (restrict_regs_of_mem availableX).symm).trans getX
  have rawGetY : fr.getAs y ty = .ok v :=
    (getAs_congr (fr := restrict fr (availOf f (availIn f result.ctx) bi j)) (fr' := fr)
      (x := y) (ty := ty) (restrict_regs_of_mem availableY).symm).trans getY
  have restored := sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have eval' : instOutcome env cp fr cm (.select ty c x y) =
      .ok ([⟨ty,Clif.Sem.select test u v⟩],cm) := by
    simp [instOutcome,Clif.evalInst,Clif.Frame.get,getAs_ok rawGetC,rawGetX,rawGetY]
  rw [eval'] at evaluated
  cases evaluated
  obtain ⟨d,output,lower,upper,execution⟩ := stock_lower_select_parameter_available_values run scope dominated events records
    foundBlock foundStmt current source clif conditionWidth typed parameter results statementResults mapped
    recorded emitted refines dfg getC getX getY held
  refine ⟨d,output,lower,upper,rfl,?_⟩
  intro world
  exact (execution world).imp (fun ρ' _ _ ⟨value,kept,post⟩ =>
    ⟨value,kept,source_single_result_values source clif results restored eval' post⟩)
end Backend.Stock.Proof.ScalarSelect
