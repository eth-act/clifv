module

public import FV.Backend.Proof.StockCountRecordValues
public import FV.Backend.Proof.StockUnarySourceValues

@[expose] public section

namespace Backend.Stock.Proof.ScalarCount
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
/-- Actual scalar count source steps consume the original body and retain
source memory; the real selected record establishes the demanded/available
post-frame through its actual result binding and final resolver. -/
theorem stock_lower_count_available_source {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f) (trailing : Bool)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt} (block : f.blocks[bi]? = some b)
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi + j)
    {info : IInfo} {x z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.unary (countOp trailing) ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (countRule trailing ty.width).id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧ v ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u : BitVec ty.width} (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (d : Nat) (ρ' : Nat → CV),step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary (countOp trailing) u⟩ (ρ' d) ∧ cm' = cm ∧
      (∀ n,n < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ n → ρ' n = ρ n) ∧
      ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx
        fr' (fun k => ρ' (aliasNum result.final.alias k)) := by
  have sourceProof := sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceProof
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have availableX := restrict_regs_isSome (by rw [getAs_ok getX]; rfl)
  have originalX : fr.getAs x ty = .ok u := by
    have same := getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := x) (ty := ty) (restrict_regs_of_mem availableX)
    exact same.symm.trans getX
  have computed : instOutcome env cp fr cm (.unary (countOp trailing) ty x) = .ok ([⟨ty,Clif.Sem.unary (countOp trailing) u⟩],cm) := by
    simp [instOutcome,Clif.evalInst,originalX]
  have equal := Prod.mk.inj (Clif.Res.ok.inj (evaluated.symm.trans computed))
  have memEq : cm' = cm := equal.2
  have evaluatedValue : instOutcome env cp fr cm (.unary (countOp trailing) ty x) =
      .ok ([⟨ty,Clif.Sem.unary (countOp trailing) u⟩],cm') := by rw [memEq]; exact computed
  obtain ⟨d,ρ',output,bounds,execution,value,kept,installed⟩ := stock_lower_count_available_values
    run scope dominated trailing events records block statement current source clif results statementResults
    mapped recorded emitted selectedId refines dfg held getX
  have post := source_single_result_values source clif results sourceStep evaluatedValue installed
  exact ⟨d,ρ',output,bounds,execution,value,memEq,kept,post⟩
/-- Original source transfer derives both operand getter and rule selection
internally; previous theorem variants remain available. -/
theorem stock_lower_count_source_by_instruction {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f) (trailing : Bool)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt} (block : f.blocks[bi]? = some b)
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi + j)
    {info : IInfo} {x z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.unary (countOp trailing) ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧ v ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (u : BitVec ty.width) (d : Nat) (ρ' : Nat → CV),
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧ step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary (countOp trailing) u⟩ (ρ' d) ∧ cm' = cm ∧
      (∀ n,n < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ n → ρ' n = ρ n) ∧
      ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx
        fr' (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have chosen := stock_selected_count_rule (stock_lower_record_context run scope events).1 trailing source clif receipt.selected
  have selectedId : step.rules.getLast? = some (countRule trailing ty.width).id := by
    rw [receipt.rules,receipt.selected.last_rule,chosen]
  obtain ⟨u,getX⟩ := stock_lower_unary_source_operand run scope dominated events block statement current source clif sourceStep
  obtain ⟨d,ρ',output,bounds,execution,value,memEq,kept,post⟩ := stock_lower_count_available_source
    run scope dominated trailing events records block statement current source clif results statementResults
    mapped recorded emitted selectedId refines dfg held getX sourceStep
  exact ⟨u,d,ρ',getX,output,bounds,execution,value,memEq,kept,post⟩

end Backend.Stock.Proof.ScalarCount
