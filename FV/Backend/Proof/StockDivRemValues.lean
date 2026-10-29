module

public import FV.Backend.Proof.StockDivRemNarrowSourceValues
public import FV.Backend.Proof.StockDivRemWideSourceValues

@[expose] public section

namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
theorem stock_lower_rem_record_values {f : Clif.Function} {result : Result}
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
      event.ctx fr (fun k => ρ (aliasNum result.final.alias k))) {u v : BitVec ty.width}
    (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    (getY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v) :
    ∃ d,step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      ∀ world,(∀ c,Clif.Sem.div (if signed then .srem else .urem) u v = .error c → TrapRun isem
        (record.output.emitted.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world c) ∧
        (∀ q,Clif.Sem.div (if signed then .srem else .urem) u v = .ok q → Runs F isem
        (record.output.emitted.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world (fun ρ' _ =>
            VHolds ⟨ty,q⟩ (ρ' d) ∧ ∀ k,k < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ k → ρ' k = ρ k)) := by
  have inv := (stock_lower_record_context run scope events).1
  have widths := (stock_div_source_data inv (if signed then .srem else .urem) source clif).1
  by_cases wide : ty.width = 64
  · have type : ty = .i64 := by
      have accepted := inv.instE _ info _ source clif
      cases ty <;> simp [Clif.Ty.width,Compile.instE,Compile.tyE] at wide accepted ⊢
    subst ty
    exact stock_lower_rem_wide_record_values run scope dominated signed events records foundBlock foundStmt current source clif results mapped recorded emitted refines dfg held getX getY
  · have narrow : ty.width ≤ 32 := by omega
    exact stock_lower_rem_narrow_record_values run scope dominated signed events records foundBlock foundStmt current narrow source clif results mapped recorded emitted refines dfg held getX getY
theorem stock_lower_rem_source_by_instruction {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f) (signed : Bool)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j) {ty : Clif.Ty} {info : IInfo} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.div (if signed then .srem else .urem) ty x y))
    (results : info.results = [z]) (statementResults : stmt.results = [z]) (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧ v ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ u v d q,step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      Clif.Sem.div (if signed then .srem else .urem) u v = .ok q ∧ cm' = cm ∧
      ∀ world,Runs F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨ty,q⟩ (ρ' d) ∧ (∀ k,k < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ k → ρ' k = ρ k) ∧
          ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx
            fr' (fun key => ρ' (aliasNum result.final.alias key))) := by
  have inv := (stock_lower_record_context run scope events).1
  have widths := (stock_div_source_data inv (if signed then .srem else .urem) source clif).1
  by_cases wide : ty.width = 64
  · have type : ty = .i64 := by
      have accepted := inv.instE _ info _ source clif
      cases ty <;> simp [Clif.Ty.width,Compile.instE,Compile.tyE] at wide accepted ⊢
    subst ty
    exact stock_lower_rem_wide_source_by_instruction run scope dominated signed events records foundBlock foundStmt current source clif results statementResults mapped recorded emitted refines dfg held sourceStep
  · have narrow : ty.width ≤ 32 := by omega
    exact stock_lower_rem_narrow_source_by_instruction run scope dominated signed events records foundBlock foundStmt current narrow source clif results statementResults mapped recorded emitted refines dfg held sourceStep
end Backend.Stock.Proof.ScalarDiv
