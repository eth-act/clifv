import FV.Backend.Proof.StockAluOperandCoverage
import FV.Backend.Proof.StockMulRecordValues
import FV.Backend.Proof.StockMulDispatch
import FV.Backend.Proof.StockGuardedRecordValues
import FV.Backend.Proof.IselFamALUA
namespace Backend.Stock.Proof.MulComplete
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
/-- Successful lowering supplies requests, selection and retained output binding;
original source execution supplies operands under the unchanged availability guard. -/
theorem record_source_framed {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary .imul ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧ cm' = cm ∧
      ValuesHeld (fun v => Demanded record.input v ∧
        v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx fr'
        (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (∀ k,k < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ k → ρ' k = ρ k) := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have chosen := selected_rule (stock_lower_record_context run scope events).1 source clif receipt.selected
  have selectedId : step.rules.getLast? = some rule_lower_871.id := by
    rw [receipt.rules,receipt.selected.last_rule,chosen]
  have sourceProof := sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceProof
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have plain : Clif.evalInst fr cm (.binary .imul ty x y) = .ok (vals,cm') := by
    simpa [instOutcome] using evaluated
  obtain ⟨u,v,getX,getY,_⟩ := evalInst_binary_inv (by rfl) plain
  have availableX := stock_lower_record_args_available run scope dominated events block statement current
    source clif x (by simp [Driver.instArgs])
  have availableY := stock_lower_record_args_available run scope dominated events block statement current
    source clif y (by simp [Driver.instArgs])
  have restrictedX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (restrict_regs_of_mem availableX)).trans getX
  have restrictedY : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (restrict_regs_of_mem availableY)).trans getY
  have computed : instOutcome env cp fr cm (.binary .imul ty x y) =
      .ok ([⟨ty,Clif.Sem.binary .imul u v⟩],cm) := by
    simp [instOutcome,Clif.evalInst,getX,getY,Clif.BinaryOp.isShift]
  have unchanged : cm' = cm := (Prod.mk.inj (Clif.Res.ok.inj (evaluated.symm.trans computed))).2
  have computed' : instOutcome env cp fr cm (.binary .imul ty x y) =
      .ok ([⟨ty,Clif.Sem.binary .imul u v⟩],cm') := by rw [unchanged]; exact computed
  obtain ⟨ρ',execution,value,kept,installed⟩ := ScalarMul.stock_lower_mul_available_values run scope dominated
    events records block statement current source clif results statementResults mapped recorded emitted selectedId
    refines held restrictedX restrictedY
  have restrictedHeld : ValuesHeld (Demanded record.output.state) event.ctx
      (restrict fr (availOf f (availIn f result.ctx) bi j)) (fun k => ρ (aliasNum result.final.alias k)) := by
    intro key demanded value lookup
    have available := restrict_regs_isSome (by rw [lookup]; rfl)
    rw [restrict_regs_of_mem available] at lookup
    exact held key ⟨demanded,available⟩ value lookup
  obtain ⟨_,_,_,_,upper,_⟩ := ScalarMul.stock_lower_mul_record_values
    run scope events records source clif results mapped recorded emitted selectedId
    refines restrictedHeld restrictedX restrictedY
  refine ⟨ρ',execution,unchanged,source_single_result_values source clif results sourceStep computed' installed,?_⟩
  intro key outside
  apply kept key
  omega

/-- Original source-transfer interface retained. -/
theorem record_source {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary .imul ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧ cm' = cm ∧
      ValuesHeld (fun v => Demanded record.input v ∧
        v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx fr'
        (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨ρ',execution,unchanged,post,_⟩ := record_source_framed run scope dominated events records
    block statement current source clif results statementResults mapped recorded emitted refines held sourceStep
  exact ⟨ρ',execution,unchanged,post⟩

end Backend.Stock.Proof.MulComplete
