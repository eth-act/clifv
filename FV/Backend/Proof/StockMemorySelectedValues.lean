import FV.Backend.Proof.StockMemorySelected
import FV.Backend.Proof.StockMemoryRecordValues

namespace Backend.Stock.Memory
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Actual selected root and original source metadata suffice for guarded memory
transfer; match, RHS, named-root and endian receipts are derived internally. -/
theorem stock_lower_load_selected_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {z a x nreg : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.load .load .i32 flags x 0)) (results : info.results = [z])
    (statementResults : stm.results = [z]) (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    (parameter : event.ctx.defInst? x = none)
    (pointer : event.ctx.valueReg? x = some (.vreg nreg .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some rule_lower_2610.id)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Backend.Proof.Sem}
    {MR : MemRelT} (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {ρ : Nat → CV} {cm cm' : Clif.Mem} {w : Arm.ArmState} {v : Clif.Val}
    (memory : MR fr.slots cm w) (dfg : DFGCons event.ctx fr)
    (operands : ValueHeld event.ctx fr (fun k => ρ (aliasNum result.final.alias k)) x)
    (held : ValuesHeld (fun y => Demanded record.output.state y ∧
      y ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    (evaluated : Clif.evalInst fr cm (.load .load .i32 flags x 0) = .ok ([v],cm')) :
    ∃ ρ' w',seqRun isem (record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w = some (.fall ρ' w') ∧
      SameWorld F w' w ∧ MR fr.slots cm' w' ∧
      VHolds v (ρ' record.input.base.nextVreg) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx (withValue fr z v)
        (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨little,out,next,trace,rhsTrace,rootRun,evalRun⟩ := stock_lower_load_selected_receipts
    run scope events records source clif recorded emitted selectedId
  exact stock_lower_parameter_load_values run scope dominated events records block statement current
    source clif results statementResults mapped parameter pointer recorded emitted
    (n := 999879) evalRun rootRun stable memorySem memoryOk memory dfg operands held little evaluated

/-- Actual load selection marks its pointer; whole-run extent and original
dominance derive both halves of the demanded/source-available operand guard. -/
theorem stock_lower_load_operand_coverage {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j)
    {info : IInfo} {z a x nreg : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.load .load .i32 flags x 0)) (results : info.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    (parameter : event.ctx.defInst? x = none) (pointer : event.ctx.valueReg? x = some (.vreg nreg .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some rule_lower_2610.id) :
    Demanded record.output.state x ∧ x ∈ availOf f (availIn f result.ctx) bi j := by
  obtain ⟨little,out,next,trace,rhsTrace,rootRun,evalRun⟩ := stock_lower_load_selected_receipts
    run scope events records source clif recorded emitted selectedId
  obtain ⟨outputs,code,upper,alias,demands⟩ := stock_lower_parameter_load_record_full run scope dominated
    events records source clif results mapped parameter pointer recorded emitted (n := 999879) evalRun rootRun
  have bound := (Extent.lower_mapped_demand_bounds run scope events records pointer).1
  have marked : Demanded (record.input.mark x) x :=
    (demanded_mark_iff record.input x x bound).mpr (Or.inl rfl)
  refine ⟨?_,stock_lower_record_args_available run scope dominated events block statement current source clif x (by simp [Driver.instArgs])⟩
  change record.output.state.demand[x]! ≠ 0
  rw [demands]
  exact marked

end Backend.Stock.Memory
