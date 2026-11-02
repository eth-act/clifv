import FV.Backend.Proof.StockFenceSourceTrap

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Complete local fence obligations for original-source proof consumers. -/
structure FenceSourceContract (f : Clif.Function) (result : Result)
    (event : BlockScanEvent) (record : ScanRecord) : Prop extends FenceRecordContract event record where
  guarded : ∀ {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem},Refines F isem →
    ∀ (env : Clif.Env) (cp : Clif.Program) (MR : MemRelT),MRStable F MR →
      ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
        (GuardedScanRel f result event.ctx event.block MR) record
  trapped : ∀ (isem : Backend.Proof.Sem) (env : Clif.Env) (cp : Clif.Program) (MR : MemRelT),
    LocalScanTrapRefines (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
      isem result.final.alias (GuardedScanRel f result event.ctx event.block MR) record

/-- The original driver run derives the source, checker and machine contracts. -/
theorem stock_lower_fence_source_contract {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} (found : event.ctx.insts[record.inst]? = some info)
    (original : info.clif = some .fence) : FenceSourceContract f result event record := by
  exact ⟨stock_lower_fence_contract run scope events records found original,
    fun hR env cp MR stable => stock_lower_fence_guarded_refines run scope dominated events records
      found original hR env cp MR stable,
    fun _ _ _ _ => stock_lower_fence_source_trap run scope events records found original⟩

end Backend.Stock.Proof
