import FV.Backend.Proof.StockMemoryStoreSourceValues

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Two retained source executions preserve their virtual files and update the same source memory relation.
The virtual files may differ in unused upper bits of narrow source values. -/
theorem stock_lower_integer_store_paired_source_step (kind : Kind) {ty : Clif.Ty}
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
    {fr fr' : Clif.Frame} {ρ otherρ : Nat → CV} {cm cm' : Clif.Mem} {w other : Arm.ArmState}
    (memory : MR fr.slots cm w) (otherMemory : MR fr.slots cm other)
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun y => Demanded record.output.state y ∧
      y ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    (otherHeld : ValuesHeld (fun y => Demanded record.output.state y ∧
      y ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr
        (fun k => otherρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ w' other',
      seqRun isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
          some (.fall ρ w') ∧
      seqRun isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) otherρ other =
          some (.fall otherρ other') ∧
      MR fr'.slots cm' w' ∧ MR fr'.slots cm' other' ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx fr'
        (fun k => ρ (aliasNum result.final.alias k)) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j+1)) event.ctx fr'
        (fun k => otherρ (aliasNum result.final.alias k)) := by
  obtain ⟨pv,w',pointer,evaluated,executed,same,memory',post⟩ := stock_lower_integer_store_source_step_of_store kind
    run scope dominated events records block statement current source clif typed
    parameter pointerMapped valueMapped recorded emitted stable memorySem memoryOk memory dfg held sourceStep
  obtain ⟨otherPointer,other',pointer',evaluated',executed',same',otherMemory',otherPost⟩ :=
    stock_lower_integer_store_source_step_of_store kind run scope dominated events records block statement current
      source clif typed parameter pointerMapped valueMapped recorded emitted stable memorySem memoryOk
      otherMemory dfg otherHeld sourceStep
  exact ⟨w',other',executed,executed',memory',otherMemory',post,otherPost⟩

end Backend.Stock.Memory.StoreRoots
