import FV.Backend.Proof.StockSelectScanRefines
import FV.Backend.Proof.StockMemoryOffsetEightStoreSourceValues

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Actual store selection discharges the existing guarded indexed scan
obligation. Original SSA/dominance derive post-source DFG; the original memory
relation supplies memory validity internally. -/
theorem stock_lower_integer_store_eight_scan_fall_refines (kind : Kind) (ty : Clif.Ty) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j)
    {info : IInfo} {value pointer valueReg pointerReg : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.store kind.sourceOp ty flags value pointer 8))
    (typed : kind.sourceOp = .store → event.ctx.valueType? value = some (.int kind.width.bits))
    (parameter : event.ctx.defInst? pointer = none)
    (pointerMapped : event.ctx.valueReg? pointer = some (.vreg pointerReg .int))
    (valueMapped : event.ctx.valueReg? value = some (.vreg valueReg .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Backend.Proof.Sem}
    {MR : MemRelT} (stable : MRStable F MR) (memorySem : StoreRefines F sb isem)
    (memoryOk : MemRelOk F sb syms f MR) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx bi) isem result.final.alias
      (GuardedScanRel f result event.ctx bi MR) record := by
  intro s s' hsource ρ w held
  obtain ⟨indexed,advance,sourceStep⟩ := hsource
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func,dfg,memory,values⟩ := held
  rw [position] at dfg values
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨pv,w',pointer,evaluated,executed,same,memory',post⟩ := stock_lower_integer_store_eight_source_step_of_store kind
    run scope dominated events records block statement current source clif typed
    parameter pointerMapped valueMapped recorded emitted stable memorySem memoryOk memory dfg values sourceStep
  refine ⟨ρ,w',executed,?_,?_,memory',?_⟩
  · obtain ⟨info',inst,vals,regs,rest,_,_,_,_,_,updated⟩ := sourceStep
    change s'.2.1 = _ at updated
    rw [updated]
    exact func
  · simpa only [advance,position] using postDFG
  · simpa only [advance,position] using post

end Backend.Stock.Memory.StoreRoots
