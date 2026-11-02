import FV.Backend.Proof.StockGuardedRecordValues
import FV.Backend.Proof.IselFamAluBShiftBase
import FV.Backend.Proof.StockAluOperandCoverage
import FV.Backend.Proof.StockShiftRecordValues
namespace Backend.Stock.Proof.ShiftComplete
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarShift
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Base shift roots preserve the original source relation. Count values keep
an arbitrary source type; execution supplies the count instead of a new premise. -/
theorem base_source_framed {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (kind : Kind) (wide : Bool) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (kind.rule wide).id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
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
  have sourceProof := sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceProof
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have plain : Clif.evalInst fr cm (.binary kind.cop ty x y) = .ok (vals,cm') := by
    cases kind <;> simpa [Kind.cop,instOutcome] using evaluated
  obtain ⟨u,amount,value,getX,getY,shift,values,unchanged⟩ :=
    evalInst_shift_ok (by cases kind <;> rfl) plain
  have valueEq : value = kind.value u amount := by
    cases kind <;> simp [Kind.cop,Kind.value,Clif.Sem.shift] at shift ⊢ <;> exact shift.symm
  have availableX := stock_lower_record_args_available run scope dominated events block statement current
    source clif x (by simp [Driver.instArgs])
  have availableY := stock_lower_record_args_available run scope dominated events block statement current
    source clif y (by simp [Driver.instArgs])
  have restrictedX : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u :=
    (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (restrict_regs_of_mem availableX)).trans getX
  have restrictedY : (restrict fr (availOf f (availIn f result.ctx) bi j)).regs y = some amount := by
    rw [restrict_regs_of_mem availableY]; exact getY
  obtain ⟨d,ρ',outputs,bounds,defs,execution,heldValue,kept,installed⟩ :=
    ScalarShift.stock_lower_shift_available_values run scope dominated events records block statement current
      kind wide source clif results statementResults mapped recorded emitted selectedId refines dfg held restrictedX restrictedY
  have computed : instOutcome env cp fr cm (.binary kind.cop ty x y) =
      .ok ([⟨ty,kind.value u amount⟩],cm') := by
    rw [← valueEq,← values]; exact evaluated
  exact ⟨ρ',execution,unchanged,source_single_result_values source clif results sourceStep computed installed,kept⟩

/-- Retained original interface. -/
theorem base_source {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (kind : Kind) (wide : Bool) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (kind.rule wide).id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ ρ', PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧ cm' = cm ∧
      ValuesHeld (fun v => Demanded record.input v ∧
        v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx fr'
        (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨ρ',execution,unchanged,post,_⟩ := base_source_framed run scope dominated events records block statement current kind wide source clif results statementResults mapped recorded emitted selectedId refines dfg held sourceStep
  exact ⟨ρ',execution,unchanged,post⟩

end Backend.Stock.Proof.ShiftComplete
