module

public import FV.Backend.Proof.StockMinMaxNarrowOriginalSourceValues

@[expose] public section

namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open MinMaxRegisterFixture Backend.Stock.Proof.ScalarCmp
/-- Original source execution supplies both getters internally; the original
reads are returned explicitly while both earlier source-transfer variants remain unchanged. -/
theorem stock_lower_minmax_narrow_source_with_reads {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} (unsigned maximum : Bool) {ty : Clif.Ty} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.binary (minmaxOperation unsigned maximum) ty x y))
    (half : Bool) (sourceTy : ty = if half then .i16 else .i8)
    (typeX : event.ctx.valueType? x = some (.int (if half then 16 else 8)))
    (typeY : event.ctx.valueType? y = some (.int (if half then 16 else 8)))
    (results : info.results = [z]) (statementResults : stmt.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun value => Demanded record.output.state value ∧ value ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun key => ρ (aliasNum result.final.alias key)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ u : BitVec ty.width,∃ v : BitVec ty.width,
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v ∧ ∃ d,step.results = [[.vreg d .int]] ∧ record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg ∧
      cm' = cm ∧
      ∀ world,Runs F isem (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨ty,Clif.Sem.binary (minmaxOperation unsigned maximum) u v⟩ (ρ' d) ∧ (∀ k,k < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ k → ρ' k = ρ k) ∧
          ValuesHeld (fun value => Demanded record.input value ∧ value ∈ availOf f (availIn f result.ctx) bi (j+1))
            event.ctx fr' (fun key => ρ' (aliasNum result.final.alias key))) := by
  obtain ⟨u,v,getX,getY⟩ := stock_lower_minmax_source_operands run scope dominated events
    foundBlock foundStmt current unsigned maximum source clif sourceStep
  obtain ⟨d,output,lower,upper,memory,execution⟩ := stock_lower_minmax_narrow_source_values run scope dominated events records
    foundBlock foundStmt current unsigned maximum source clif half sourceTy typeX typeY results statementResults mapped
    recorded emitted refines dfg getX getY held sourceStep
  exact ⟨u,v,getX,getY,d,output,lower,upper,memory,execution⟩
end Backend.Stock.Proof.ScalarSelect
