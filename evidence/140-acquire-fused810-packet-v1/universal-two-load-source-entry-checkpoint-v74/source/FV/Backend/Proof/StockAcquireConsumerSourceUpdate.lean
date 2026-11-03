import FV.Backend.Proof.StockAcquireFreshInterval

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual source construction identifies the consumer's original result names. -/
theorem source_endpoint_consumer_results {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord} (events : event ∈ result.blockScans.toList)
    (R : SourceEndpointReceipt f event record) : R.rootInfo.results = R.consumerStmt.results := by
  obtain ⟨info,installed,source,results⟩ := (ctxSpec_of R.built).facts.stmt event.block R.block R.consumerIndex
    R.consumerStmt R.blockAt R.consumerAt
  have view := stock_lower_event_build_source_slots run scope events R.built
  have actual : event.ctx.insts[record.inst]? = some info := by
    rw [R.current]
    exact view _ info R.consumerStmt.inst installed source
  have same := Option.some.inj (actual.symm.trans R.rootInstalled)
  rw [same] at results
  exact results

/-- A singleton original source result preserves its exact memory and register update. -/
theorem source_single_result_update {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    {slot value : Nat} {info : IInfo} {inst : Clif.Inst} {before after : Clif.Frame × Clif.Mem}
    {result : Clif.Val} (installed : ctx.insts[slot]? = some info) (source : info.clif = some inst)
    (results : info.results = [value]) (executed : SourceInstResult env program ctx slot before after)
    (evaluated : instOutcome env program before.1 before.2 inst = .ok ([result],before.2)) :
    after.2 = before.2 ∧ after.1.regs = (withValue before.1 value result).regs := by
  obtain ⟨actual,actualInst,values,regs,rest,actualAt,actualSource,body,outcome,written,frame⟩ := executed
  have infoEq := Option.some.inj (actualAt.symm.trans installed)
  subst actual
  have instEq := Option.some.inj (actualSource.symm.trans source)
  subst actualInst
  have same := Clif.Res.ok.inj (outcome.symm.trans evaluated)
  obtain ⟨valuesEq,memoryEq⟩ := Prod.mk.inj same
  rw [results,valuesEq] at written
  simp only [Clif.Regs.setMany,Option.some.injEq] at written
  refine ⟨memoryEq,?_⟩
  rw [frame,← written]
  rfl

/-- Source frame transport retains the complete pending value relation. -/
theorem pending_values_frame_regs {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    {snapshots : List (SunkReadSnapshot ctx env program)} {demand : Nat → Prop}
    {before after : Clif.Frame} {regs : Nat → CV}
    (same : after.regs = before.regs) (held : PendingValuesHeld snapshots demand before regs) :
    PendingValuesHeld snapshots demand after regs := by
  intro value required notSuspended v found
  rw [same] at found
  exact held value required notSuspended v found

end Backend.Stock.Proof.Acquire810
