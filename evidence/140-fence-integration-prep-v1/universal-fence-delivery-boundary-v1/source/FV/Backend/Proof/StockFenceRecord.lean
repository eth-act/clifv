import FV.Backend.Proof.StockFenceRecordOrigin
import FV.Backend.Proof.StockFenceScan
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction commitOpportunistic
/-- Every actual retained source fence emits; demand does not control this decision. -/
theorem stock_lower_fence_emission {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} (found : event.ctx.insts[record.inst]? = some info)
    (source : info.clif = some .fence) :
    ∃ emission, emitInstruction event.ctx record.inst (scanState record.input record.inst) = .ok emission ∧
      record.output = emission.scan event.block record.inst (scanState record.input record.inst) := by
  have original := (stock_lower_record_context run scope events).2.2 _ _ _ found source
  have unsunk := ((SinkRules.stock_lower_fence_unsunk run scope original source).2 event events).2 record records
  have different := stock_fence_source_not_term run events found source
  apply stock_mandatory_scan_emission unsunk.1 different ?_ (stock_fence_record_execute run events records)
  have lookup : event.ctx.insts[record.inst]! = info := by simp only [getElem!_def,found,Option.getD_some]
  rw [lookup,source]
  rfl

end Backend.Stock.Proof
