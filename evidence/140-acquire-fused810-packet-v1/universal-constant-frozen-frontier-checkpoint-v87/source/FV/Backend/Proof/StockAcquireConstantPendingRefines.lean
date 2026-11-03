import FV.Backend.Proof.StockAcquireConstantPendingSource
import FV.Backend.Proof.StockConstantScanRefines

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Actual integer constants advance the source-indexed pending relation.
The full capture history and every required nonsuspended binding remain in the relation. -/
theorem stock_lower_constant_pending_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {ty : Clif.Ty} {imm : BitVec ty.width} {x a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.iconst ty imm))
    (results : info.results = [x]) (statementResults : stm.results = [x])
    (mapped : event.ctx.valueReg? x = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program}
    (snapshots : List (Acquire810.SunkReadSnapshot event.ctx env cp)) :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx bi) isem result.final.alias
      (Acquire810.PendingGuardedScanRel f result event.ctx bi env cp MR snapshots) record := by
  have semantics : ∀ aliases i, isem (i.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size + 1))) = isem i := by
    intro aliases i
    apply driver.rename _ (aliasNum aliases) ?_ i
    refine ⟨fun n c => resolve_vreg aliases _ n c, ?_⟩
    intro r hr
    cases r with
    | vreg n c => exact False.elim (hr n c rfl)
    | _ => simp [Backend.lowerFunction.resolve]
  obtain ⟨_,_,_,transfer⟩ := stock_lower_constant_pending_source run scope dominated events records block statement current
    source clif statementResults results mapped recorded emitted refines semantics env cp snapshots
  intro s s' hsource ρ w held
  obtain ⟨indexed, advance, sourceStep⟩ := hsource
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func, dfg, memory, values⟩ := held
  rw [position] at dfg values
  obtain ⟨ρ',w',executed,postMemory,post⟩ := transfer (fun cm w => MR s.2.1.slots cm w)
    (fun cm w w' world mem => stable _ _ _ _ (SameWorld.nf world) mem)
    _ _ _ _ ρ w sourceStep memory values
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have func' : s'.2.1.func = f := by rw [updated]; exact func
  have slots : s'.2.1.slots = s.2.1.slots := by rw [updated]
  refine ⟨ρ',w',executed,func',?_,?_,?_⟩
  · simpa only [advance,position] using postDFG
  · rw [slots]; exact postMemory
  · simpa only [advance,position] using post


end Backend.Stock.Proof
