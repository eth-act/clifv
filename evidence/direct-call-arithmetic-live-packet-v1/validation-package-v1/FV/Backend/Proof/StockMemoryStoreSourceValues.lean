import FV.Backend.Proof.StockMemoryStoreCoverage
import FV.Backend.Proof.StockMemoryStoreRecordExec
import FV.Backend.Proof.StockGuardedRecordValues

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem statement_results {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {record : ScanRecord}
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j) {info : IInfo} {inst : Clif.Inst}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some inst)
    (empty : info.results = []) : stm.results = [] := by
  have globalSource := (stock_lower_record_context run scope events).2.2 _ _ _ source clif
  rw [current] at globalSource
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,
    label,nodeBi,data,core,build,ordered,initial,none,parts,folded,
    final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ := stock_lower_blockScanOrigin run events
  obtain ⟨original,st0,old,spec,view⟩ := buildCtx_source build
  obtain ⟨other,otherSource,otherClif,otherResults⟩ := spec.facts.stmt bi b j stm block statement
  have actualSource : original.insts[blockStart f bi+j]? = some info := by
    rw [← view.insts]
    exact globalSource
  cases Option.some.inj (otherSource.symm.trans actualSource)
  simpa only [empty] using otherResults.symm

/-- An original source store transfers updated memory and guarded values through its actual retained record. -/
theorem stock_lower_integer_store_source_step_of_store (kind : Kind) {ty : Clif.Ty}
    {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) (scope : LowerScope f)
    (dominated : Dominated f) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j)
    {info : IInfo} {value pointer valueReg pointerReg : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.store kind.sourceOp ty flags value pointer 0))
    (typed : kind.sourceOp = .store → event.ctx.valueType? value = some (.int kind.width.bits))
    (parameter : event.ctx.defInst? pointer = none)
    (pointerMapped : event.ctx.valueReg? pointer = some (.vreg pointerReg .int))
    (valueMapped : event.ctx.valueReg? value = some (.vreg valueReg .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Backend.Proof.Sem}
    {MR : MemRelT} (stable : MRStable F MR) (memorySem : StoreRefines F sb isem)
    (memoryOk : MemRelOk F sb syms f MR)
    {fr fr' : Clif.Frame} {ρ : Nat → CV} {cm cm' : Clif.Mem} {w : Arm.ArmState}
    (memory : MR fr.slots cm w)
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun y => Demanded record.output.state y ∧
      y ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ pv w',fr.regs pointer = some pv ∧
      Clif.evalInst fr cm (.store kind.sourceOp ty flags value pointer 0) = .ok ([],cm') ∧
      seqRun isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
          some (.fall ρ w') ∧
      SameWorld F w' (Arm.write_mem_bytes kind.storeOp.bytes (BitVec.ofNat 64 (Clif.effAddr pv 0))
        ((lo64 (ρ (aliasNum result.final.alias valueReg))).setWidth (kind.storeOp.bytes * 8)) w) ∧
      MR fr'.slots cm' w' ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx fr'
        (fun k => ρ (aliasNum result.final.alias k)) := by
  have required := stock_lower_integer_store_operand_coverage kind run scope dominated events records
    block statement current source clif typed parameter pointerMapped valueMapped recorded emitted
  have needValue := required value (Or.inl rfl)
  have needPointer := required pointer (Or.inr rfl)
  have little := (integer_store_source_data kind (stock_lower_record_context run scope events).1 source clif).1
  have empty := (stock_lower_integer_store_record_full kind run scope events records source clif typed
    parameter pointerMapped valueMapped recorded emitted).1
  have statementEmpty := statement_results run scope events block statement current source clif empty
  obtain ⟨info',inst,vals,regs,rest,found,original,body,outcome,written,updated⟩ := sourceStep
  cases Option.some.inj (found.symm.trans source)
  cases Option.some.inj (original.symm.trans clif)
  have plain : Clif.evalInst fr cm (.store kind.sourceOp ty flags value pointer 0) = .ok (vals,cm') := by
    simpa only [instOutcome] using outcome
  obtain ⟨_,_,_,_,_,_,noValues,_⟩ := evalInst_store_inv little plain
  rw [noValues,empty] at written
  simp only [Clif.Regs.setMany_nil,Option.some.injEq] at written
  subst regs
  change fr' = _ at updated
  have frameRegs : fr'.regs = fr.regs := by rw [updated]
  have frameSlots : fr'.slots = fr.slots := by rw [updated]
  have restrictedPointer : (restrict fr (availOf f (availIn f result.ctx) bi j)).get pointer = fr.get pointer := by
    simp only [Clif.Frame.get,restrict_regs_of_mem needPointer.2]
  have restrictedValue : (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs value ty = fr.getAs value ty := by
    simp only [Clif.Frame.getAs,Clif.Frame.get,restrict_regs_of_mem needValue.2]
  have restrictedEval : Clif.evalInst (restrict fr (availOf f (availIn f result.ctx) bi j)) cm
      (.store kind.sourceOp ty flags value pointer 0) = .ok (vals,cm') := by
    simpa only [Clif.evalInst,restrictedPointer,restrictedValue] using plain
  have restrictedHeld : ValuesHeld (fun y => Demanded record.output.state y ∧
      y ∈ availOf f (availIn f result.ctx) bi j) event.ctx
      (restrict fr (availOf f (availIn f result.ctx) bi j)) (fun k => ρ (aliasNum result.final.alias k)) := by
    intro y needed val lookup
    rw [restrict_regs_of_mem needed.2] at lookup
    exact held y needed val lookup
  obtain ⟨pv,w',pointer,executed,same,memory',_⟩ := stock_lower_integer_store_record_run_of_store kind run scope events records
    source clif typed parameter pointerMapped valueMapped recorded emitted stable memorySem memoryOk
    (fr := restrict fr (availOf f (availIn f result.ctx) bi j)) memory dfg
    (restrictedHeld pointer needPointer) (restrictedHeld value needValue) restrictedEval
  refine ⟨pv,w',?_,?_,executed,same,?_,?_⟩
  · simpa only [restrict_regs_of_mem needPointer.2] using pointer
  · simpa only [noValues] using plain
  · simpa only [frameSlots,restrict] using memory'
  · intro y needed val lookup
    rw [frameRegs] at lookup
    have before := available_before_of_after_not_result block statement needed.2 (by simp [statementEmpty])
    have demanded : Demanded record.output.state y := by
      intro zero
      have count := stock_lower_record_demand_mono run events records recorded emitted y
      change record.output.state.demand[y]! = 0 at zero
      rw [zero] at count
      exact needed.1 (Nat.eq_zero_of_le_zero count)
    exact held y ⟨demanded,before⟩ val lookup

/-- Preserve the original source-step interface for the unguarded memory semantics. -/
theorem stock_lower_integer_store_source_step (kind : Kind) {ty : Clif.Ty}
    {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) (scope : LowerScope f)
    (dominated : Dominated f) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j)
    {info : IInfo} {value pointer valueReg pointerReg : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.store kind.sourceOp ty flags value pointer 0))
    (typed : kind.sourceOp = .store → event.ctx.valueType? value = some (.int kind.width.bits))
    (parameter : event.ctx.defInst? pointer = none)
    (pointerMapped : event.ctx.valueReg? pointer = some (.vreg pointerReg .int))
    (valueMapped : event.ctx.valueReg? value = some (.vreg valueReg .int))
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
    ∃ pv w',fr.regs pointer = some pv ∧
      Clif.evalInst fr cm (.store kind.sourceOp ty flags value pointer 0) = .ok ([],cm') ∧
      seqRun isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
          some (.fall ρ w') ∧
      SameWorld F w' (Arm.write_mem_bytes kind.storeOp.bytes (BitVec.ofNat 64 (Clif.effAddr pv 0))
        ((lo64 (ρ (aliasNum result.final.alias valueReg))).setWidth (kind.storeOp.bytes * 8)) w) ∧
      MR fr'.slots cm' w' ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx fr'
        (fun k => ρ (aliasNum result.final.alias k)) := by
  exact stock_lower_integer_store_source_step_of_store kind run scope dominated events records block statement
    current source clif typed parameter pointerMapped valueMapped recorded emitted stable
    (store_refines_of_mem memorySem) memoryOk memory dfg held sourceStep

end Backend.Stock.Memory.StoreRoots
