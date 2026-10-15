import FV.Backend.Proof.StockDivSignedSourceValues
import FV.Backend.Proof.StockDivSourceTrap
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
theorem stock_lower_sdiv_source_trap {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j) {ty : Clif.Ty} {info : IInfo} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.div .sdiv ty x y))
    (results : info.results = [z]) (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧ v ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {cm : Clif.Mem} {code : Clif.TrapCode}
    (sourceTrap : instOutcome env cp fr cm (.div .sdiv ty x y) = .trap code) :
    ∃ d,step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      ∀ world,TrapRun isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world code := by
  obtain ⟨u,v,getX,getY,failed⟩ := stock_lower_div_trap_operands run scope dominated events
    foundBlock foundStmt current source clif sourceTrap
  obtain ⟨d,output,bounds,execution⟩ := stock_lower_sdiv_record_values run scope dominated  events records
    foundBlock foundStmt current source clif results mapped recorded emitted refines dfg held getX getY
  exact ⟨d,output,bounds,fun world => (execution world).1 code failed⟩
end Backend.Stock.Proof.ScalarDiv
