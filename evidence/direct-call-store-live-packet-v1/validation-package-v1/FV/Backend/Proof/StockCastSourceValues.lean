import FV.Backend.Proof.StockCastRecordValues
namespace Backend.Stock.Proof.ScalarCast
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
/-- The original successful source step supplies its widening condition and
actual post-frame internally; no additional accepted-input premise is needed. -/
theorem stock_lower_extend_available_source {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt} (block : f.blocks[bi]? = some b)
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi + j)
    (sg : Bool) {info : IInfo} {x z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.extend (extendOp sg) ty x))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some (extendRule sg).id)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j))) {ρ : Nat → CV}
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧ v ∈ availOf f (availIn f result.ctx) bi j)
      event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {val : Clif.Val} (getX : (restrict fr (availOf f (availIn f result.ctx) bi j)).regs x = some val)
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (d : Nat) (ρ' : Nat → CV),step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,extendBits sg ty.width val.bits⟩ (ρ' d) ∧
      (∀ n,n < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ n → ρ' n = ρ n) ∧
      ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx
        fr' (fun k => ρ' (aliasNum result.final.alias k)) := by
  have sourceProof := sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceProof
  have sameInfo := Option.some.inj (found.symm.trans source)
  subst info'
  have sameInst := Option.some.inj (original.symm.trans clif)
  subst inst
  have rawEval : Clif.evalInst fr cm (.extend (extendOp sg) ty x) = .ok (vals,cm') := by
    simpa only [instOutcome] using evaluated
  obtain ⟨input,inputLookup,grows,memEq,valuesEq⟩ := evalInst_extend_ok rawEval
  have availableX := restrict_regs_isSome (by rw [getX]; rfl)
  have originalX : fr.regs x = some val := by
    have known := getX
    rw [restrict_regs_of_mem availableX] at known
    exact known
  have sameInput := Option.some.inj (inputLookup.symm.trans originalX)
  subst input
  have valueEq : extVal_fb (extendOp sg) ty val.bits = extendBits sg ty.width val.bits := by
    cases sg <;> rfl
  rw [valueEq] at valuesEq
  have evaluatedValue := evaluated
  rw [valuesEq] at evaluatedValue
  obtain ⟨d,ρ',output,bounds,execution,value,kept,installed⟩ := stock_lower_extend_available_values
    run scope dominated events records block statement current sg source clif results statementResults
    mapped recorded emitted selectedId refines dfg held getX grows
  have post := source_single_result_values source clif results sourceStep evaluatedValue installed
  exact ⟨d,ρ',output,bounds,execution,value,kept,post⟩
end Backend.Stock.Proof.ScalarCast
