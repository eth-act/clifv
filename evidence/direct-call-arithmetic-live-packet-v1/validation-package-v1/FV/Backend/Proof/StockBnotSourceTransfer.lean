import FV.Backend.Proof.StockAluOperandCoverage
import FV.Backend.Proof.StockBnotRecordValues
import FV.Backend.Proof.StockLogicalNotXorRecord
import FV.Backend.Proof.StockBnotDispatch
import FV.Backend.Proof.StockGuardedRecordValues
import FV.Backend.Proof.IselFamALUALogicNot
namespace Backend.Stock.Proof.BnotComplete
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
theorem source_operands {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord} (events : event ∈ result.blockScans.toList)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt} (block : f.blocks[bi]? = some b)
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi + j)
    {info : IInfo} {ty : Clif.Ty} {x : Nat}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.unary .bnot ty x))
    {env : Clif.Env} {cp : Clif.Program} {fr fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ u,(restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u := by
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have plain : Clif.evalInst fr cm (.unary .bnot ty x) = .ok (vals,cm') := by
    simpa [instOutcome] using evaluated
  obtain ⟨u,getX,_⟩ := evalInst_unary_inv plain
  have availableX : x ∈ availOf f (availIn f result.ctx) bi j := stock_lower_record_args_available
    run scope dominated events block statement current source clif x (by simp [Driver.instArgs])
  exact ⟨u,(getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := x) (ty := ty) (restrict_regs_of_mem availableX)).trans getX⟩
theorem available_source {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {x z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.unary .bnot ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {u : BitVec ty.width}
    (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u)
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bnot u⟩ (ρ' record.input.base.nextVreg) ∧
      cm' = cm ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          fr'
          (fun k => ρ' (aliasNum result.final.alias k)) := by
  have sourceProof := sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceProof
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have availableX := restrict_regs_isSome (by rw [getAs_ok getX]; rfl)
  have originalX : fr.getAs x ty = .ok u :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := x) (ty := ty) (restrict_regs_of_mem availableX)).symm.trans getX
  have computed : instOutcome env cp fr cm (.unary .bnot ty x) =
      .ok ([⟨ty,Clif.Sem.unary .bnot u⟩],cm) := by
    simp [instOutcome,Clif.evalInst,originalX]
  have equal := Prod.mk.inj (Clif.Res.ok.inj (evaluated.symm.trans computed))
  have memEq : cm' = cm := equal.2
  have evaluatedValue : instOutcome env cp fr cm (.unary .bnot ty x) =
      .ok ([⟨ty,Clif.Sem.unary .bnot u⟩],cm') := by rw [memEq]; exact computed
  have inventory := record_selected_rule_ids run scope events records source clif recorded emitted
  obtain ⟨id,last,member⟩ : ∃ id, step.rules.getLast? = some id ∧ id ∈ candidateIds := by
    simpa only [Option.any_eq_true,List.contains_iff_mem] using inventory
  have values : ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bnot u⟩ (ρ' record.input.base.nextVreg) ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧ y ∈ availOf f (availIn f result.ctx) bi (j+1))
        event.ctx (withValue fr z ⟨ty,Clif.Sem.unary .bnot u⟩)
        (fun k => ρ' (aliasNum result.final.alias k)) := by
    simp only [candidateIds,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact LogicalNot.stock_lower_not_xor_available_values run scope dominated events records block statement current
        source clif results statementResults mapped recorded emitted last refines dfg held getX
    · exact Bnot.stock_lower_bnot_available_values run scope dominated events records block statement current
        true source clif results statementResults mapped recorded emitted last refines dfg held getX
    · exact Bnot.stock_lower_bnot_available_values run scope dominated events records block statement current
        false source clif results statementResults mapped recorded emitted last refines dfg held getX
  obtain ⟨ρ',execution,value,kept,installed⟩ := values
  have post := source_single_result_values source clif results sourceStep evaluatedValue installed
  exact ⟨ρ',execution,value,memEq,kept,post⟩
theorem source_from_step {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {x z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.unary .bnot ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (u : BitVec ty.width) (ρ' : Nat → CV),
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧ PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bnot u⟩ (ρ' record.input.base.nextVreg) ∧
      cm' = cm ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          fr'
          (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨u,getX⟩ := source_operands run scope dominated events block statement current source clif sourceStep
  obtain ⟨ρ',execution,value,memEq,kept,post⟩ := available_source
    run scope dominated events records block statement current source clif results statementResults
    mapped recorded emitted refines dfg held getX sourceStep
  exact ⟨u,ρ',getX,execution,value,memEq,kept,post⟩

end Backend.Stock.Proof.BnotComplete
