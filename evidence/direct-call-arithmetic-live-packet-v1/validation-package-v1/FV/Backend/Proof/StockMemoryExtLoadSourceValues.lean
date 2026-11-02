import FV.Backend.Proof.StockMemoryExtLoadSelectedValues

namespace Backend.Stock.Memory.ExtendedRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- A real original load step supplies its value and memory behavior. Restricted
DFG and the ordinary guarded value invariant suffice; pointer availability and
demand, typed selection, binding and final aliases are all derived internally. -/
theorem stock_lower_extending_load_source_step (kind : Kind) {ty : Clif.Ty} {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j)
    {info : IInfo} {z a x nreg : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.load kind.sourceOp ty flags x 0)) (results : info.results = [z])
    (statementResults : stm.results = [z]) (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    (parameter : event.ctx.defInst? x = none) (pointer : event.ctx.valueReg? x = some (.vreg nreg .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Backend.Proof.Sem}
    {MR : MemRelT} (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR)
    {fr fr' : Clif.Frame} {ρ : Nat → CV} {cm cm' : Clif.Mem} {w : Arm.ArmState}
    (memory : MR fr.slots cm w)
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun y => Demanded record.output.state y ∧
      y ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (v : Clif.Val) (ρ' : Nat → CV) (w' : Arm.ArmState),
      Clif.evalInst fr cm (.load kind.sourceOp ty flags x 0) = .ok ([v],cm') ∧
      seqRun isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w = some (.fall ρ' w') ∧
      SameWorld F w' w ∧ MR fr'.slots cm' w' ∧ VHolds v (ρ' record.input.base.nextVreg) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx fr'
        (fun k => ρ' (aliasNum result.final.alias k)) := by
  have required := stock_lower_extending_load_operand_coverage kind run scope dominated events records block statement current
    source clif results mapped parameter pointer recorded emitted
  have little := (stock_lower_extending_load_selected_receipts kind run scope events records source clif recorded emitted).1
  have sourceProof := sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,outcome,written,updated⟩ := sourceProof
  cases Option.some.inj (found.symm.trans source)
  cases Option.some.inj (original.symm.trans clif)
  have plain : Clif.evalInst fr cm (.load kind.sourceOp ty flags x 0) = .ok (vals,cm') := by
    simpa only [instOutcome] using outcome
  obtain ⟨pv,raw,hpv,size,valid,read,valsEq,memEq⟩ := evalInst_load_inv little plain
  have one : ∃ v,vals = [v] := ⟨_,valsEq⟩
  obtain ⟨v,rfl⟩ := one
  have restrictedGet : (restrict fr (availOf f (availIn f result.ctx) bi j)).get x = fr.get x := by
    simp only [Clif.Frame.get,restrict_regs_of_mem required.2]
  have restrictedEval : Clif.evalInst (restrict fr (availOf f (availIn f result.ctx) bi j)) cm
      (.load kind.sourceOp ty flags x 0) = .ok ([v],cm') := by
    simpa only [Clif.evalInst,restrictedGet] using plain
  have restrictedHeld : ValuesHeld (fun y => Demanded record.output.state y ∧
      y ∈ availOf f (availIn f result.ctx) bi j) event.ctx
      (restrict fr (availOf f (availIn f result.ctx) bi j)) (fun k => ρ (aliasNum result.final.alias k)) := by
    intro y needed value lookup
    rw [restrict_regs_of_mem needed.2] at lookup
    exact held y needed value lookup
  have operands := restrictedHeld x required
  obtain ⟨ρ',w',executed,same,memory',value,post⟩ := stock_lower_extending_load_selected_values kind
    run scope dominated events records block statement current source clif results statementResults mapped
    parameter pointer recorded emitted stable memorySem memoryOk
    (fr := restrict fr (availOf f (availIn f result.ctx) bi j)) memory dfg operands restrictedHeld restrictedEval
  have installed : ValuesHeld (fun y => Demanded record.input y ∧
      y ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx (withValue fr z v)
      (fun k => ρ' (aliasNum result.final.alias k)) := by
    intro y needed val lookup
    by_cases equal : y = z
    · subst y
      have lookup' : (withValue (restrict fr (availOf f (availIn f result.ctx) bi j)) z v).regs z = some val := by
        simpa only [withValue,ite_true,eq_self] using lookup
      exact post z needed val lookup'
    · have before := available_before_of_after_not_result block statement needed.2
        (by simpa only [statementResults,List.mem_singleton] using equal)
      have lookup' : (withValue (restrict fr (availOf f (availIn f result.ctx) bi j)) z v).regs y = some val := by
        simpa only [withValue,ite_eq_right equal,restrict_regs_of_mem before] using lookup
      exact post y needed val lookup'
  have sourceOutcome : instOutcome env cp fr cm (.load kind.sourceOp ty flags x 0) = .ok ([v],cm') := by
    simpa only [instOutcome] using plain
  refine ⟨v,ρ',w',plain,executed,same,?_,value,
    source_single_result_values source clif results sourceStep sourceOutcome installed⟩
  change fr' = _ at updated
  rw [updated]
  exact memory'

end Backend.Stock.Memory.ExtendedRoots
