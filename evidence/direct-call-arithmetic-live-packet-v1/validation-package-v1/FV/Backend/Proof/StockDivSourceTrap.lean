import FV.Backend.Proof.StockDivRemValues
import FV.Backend.Proof.StockDivUdivValues
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
theorem stock_lower_div_trap_operands {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord} (events : event ∈ result.blockScans.toList)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j) {ty : Clif.Ty} {op : Clif.DivOp} {info : IInfo} {x y : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.div op ty x y))
    {env : Clif.Env} {cp : Clif.Program} {fr : Clif.Frame} {cm : Clif.Mem} {code : Clif.TrapCode}
    (sourceTrap : instOutcome env cp fr cm (.div op ty x y) = .trap code) :
    ∃ u v,(restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v ∧ Clif.Sem.div op u v = .error code := by
  have plain : Clif.evalInst fr cm (.div op ty x y) = .trap code := sourceTrap
  obtain ⟨u,v,lookupX,lookupY,evaluated⟩ := evalInst_div_inv plain (fun _ impossible => by cases impossible)
  have getX : fr.getAs x ty = .ok u := by
    unfold Clif.Frame.getAs Clif.Frame.get
    rw [lookupX]
    simp [Clif.Res.ofOption]
  have getY : fr.getAs y ty = .ok v := by
    unfold Clif.Frame.getAs Clif.Frame.get
    rw [lookupY]
    simp [Clif.Res.ofOption]
  have availableX := stock_lower_record_args_available run scope dominated events foundBlock foundStmt current source clif x (by simp [Driver.instArgs])
  have availableY := stock_lower_record_args_available run scope dominated events foundBlock foundStmt current source clif y (by simp [Driver.instArgs])
  have failed : Clif.Sem.div op u v = .error code := by
    cases division : Clif.Sem.div op u v with
    | error c => rw [division] at evaluated; cases evaluated; rfl
    | ok q => rw [division] at evaluated; cases evaluated
  exact ⟨u,v,(getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := x) (ty := ty) (restrict_regs_of_mem availableX)).trans getX,
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := y) (ty := ty) (restrict_regs_of_mem availableY)).trans getY,failed⟩
theorem stock_lower_udiv_source_trap {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j) {ty : Clif.Ty} {info : IInfo} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.div .udiv ty x y))
    (results : info.results = [z]) (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧ v ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {cm : Clif.Mem} {code : Clif.TrapCode}
    (sourceTrap : instOutcome env cp fr cm (.div .udiv ty x y) = .trap code) :
    ∃ d,step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      ∀ world,TrapRun isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world code := by
  obtain ⟨u,v,getX,getY,failed⟩ := stock_lower_div_trap_operands run scope dominated events
    foundBlock foundStmt current source clif sourceTrap
  obtain ⟨d,output,bounds,execution⟩ := stock_lower_udiv_record_values run scope dominated  events records
    foundBlock foundStmt current source clif results mapped recorded emitted refines dfg held getX getY
  exact ⟨d,output,bounds,fun world => (execution world).1 code failed⟩
theorem stock_lower_rem_source_trap {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f) (signed : Bool)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j) {ty : Clif.Ty} {info : IInfo} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.div (if signed then .srem else .urem) ty x y))
    (results : info.results = [z]) (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧ v ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {cm : Clif.Mem} {code : Clif.TrapCode}
    (sourceTrap : instOutcome env cp fr cm (.div (if signed then .srem else .urem) ty x y) = .trap code) :
    ∃ d,step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      ∀ world,TrapRun isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world code := by
  obtain ⟨u,v,getX,getY,failed⟩ := stock_lower_div_trap_operands run scope dominated events
    foundBlock foundStmt current source clif sourceTrap
  obtain ⟨d,output,bounds,execution⟩ := stock_lower_rem_record_values run scope dominated signed events records
    foundBlock foundStmt current source clif results mapped recorded emitted refines dfg held getX getY
  exact ⟨d,output,bounds,fun world => (execution world).1 code failed⟩
end Backend.Stock.Proof.ScalarDiv
