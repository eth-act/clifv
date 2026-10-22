import FV.Backend.Proof.StockDivSignedSourceTrap
import FV.Backend.Proof.StockDivUdivWideSourceValues
import FV.Backend.Proof.StockDivUdivNarrowSourceValues
import FV.Backend.Proof.StockDivRemWideSourceValues
import FV.Backend.Proof.StockDivRemNarrowSourceValues
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

theorem stock_lower_div_source_by_instruction {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j) {op : Clif.DivOp} {ty : Clif.Ty} {info : IInfo} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.div op ty x y))
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
      Clif.Sem.div op u v = .ok q ∧ cm' = cm ∧
      ∀ world,Runs F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨ty,q⟩ (ρ' d) ∧ (∀ k,k < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ k → ρ' k = ρ k) ∧
          ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx
            fr' (fun key => ρ' (aliasNum result.final.alias key))) := by
  have inv := (stock_lower_record_context run scope events).1
  have supported : eTy ty = true := by
    cases op <;> simpa [Compile.instE,Compile.tyE,eTy] using inv.instE _ info _ source clif
  have width : ty = .i64 ∨ ty.width ≤ 32 := by
    cases ty <;> simp_all [eTy,Clif.Ty.width]
  cases op with
  | sdiv =>
    exact stock_lower_sdiv_source_by_instruction run scope dominated events records foundBlock foundStmt current source clif results statementResults mapped recorded emitted refines dfg held sourceStep
  | udiv =>
    rcases width with rfl | narrow
    · exact stock_lower_udiv_wide_source_by_instruction run scope dominated events records foundBlock foundStmt current source clif results statementResults mapped recorded emitted refines dfg held sourceStep
    · exact stock_lower_udiv_narrow_source_by_instruction run scope dominated events records foundBlock foundStmt current narrow source clif results statementResults mapped recorded emitted refines dfg held sourceStep
  | srem =>
    rcases width with rfl | narrow
    · exact stock_lower_rem_wide_source_by_instruction run scope dominated (true) events records foundBlock foundStmt current source clif results statementResults mapped recorded emitted refines dfg held sourceStep
    · exact stock_lower_rem_narrow_source_by_instruction run scope dominated (true) events records foundBlock foundStmt current narrow source clif results statementResults mapped recorded emitted refines dfg held sourceStep
  | urem =>
    rcases width with rfl | narrow
    · exact stock_lower_rem_wide_source_by_instruction run scope dominated (false) events records foundBlock foundStmt current source clif results statementResults mapped recorded emitted refines dfg held sourceStep
    · exact stock_lower_rem_narrow_source_by_instruction run scope dominated (false) events records foundBlock foundStmt current narrow source clif results statementResults mapped recorded emitted refines dfg held sourceStep

theorem stock_lower_div_source_trap {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j) {op : Clif.DivOp} {ty : Clif.Ty} {info : IInfo} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.div op ty x y))
    (results : info.results = [z]) (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧ v ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {cm : Clif.Mem} {code : Clif.TrapCode}
    (sourceTrap : instOutcome env cp fr cm (.div op ty x y) = .trap code) :
    ∃ d,step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      ∀ world,TrapRun isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world code := by
  cases op with
  | sdiv =>
    exact stock_lower_sdiv_source_trap run scope dominated events records
      foundBlock foundStmt current source clif results mapped recorded emitted refines dfg held sourceTrap
  | udiv =>
    exact stock_lower_udiv_source_trap run scope dominated events records
      foundBlock foundStmt current source clif results mapped recorded emitted refines dfg held sourceTrap
  | srem =>
    exact stock_lower_rem_source_trap run scope dominated true events records
      foundBlock foundStmt current source clif results mapped recorded emitted refines dfg held sourceTrap
  | urem =>
    exact stock_lower_rem_source_trap run scope dominated false events records
      foundBlock foundStmt current source clif results mapped recorded emitted refines dfg held sourceTrap

end Backend.Stock.Proof.ScalarDiv
