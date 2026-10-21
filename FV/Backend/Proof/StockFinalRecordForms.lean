import FV.Backend.Proof.StockResolvedRecordForms
import FV.Backend.Proof.StockBlockCode

namespace Backend.Stock.Proof.Coverage.Result
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Backend.Proof.Spill
open Isle Isle.Interp Isle.Aarch64

/-- Each actual source record has a concrete segment in the returned VCode,
and every instruction in that segment is covered and ordinarily spill-valid.
Final aliases and block placement are derived from the successful driver. -/
theorem stock_lower_source_record_final_segment
    {f : Clif.Function} {result : Backend.Stock.Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {inst : Clif.Inst} (source : event.ctx.insts[record.inst]? = some info)
    (original : info.clif = some inst) :
    ∃ (label : Nat) (block : VBlock) (k : Nat), result.code.blocks[label]? = some block ∧
      SegAt block k (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ∧
      ∀ i ∈ record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))),
        Covered i = true ∧ (i.isCtl = false → SpillInstOk i) := by
  obtain ⟨label,block,k,placed,segment⟩ := stock_lower_record_segment run events records
  exact ⟨label,block,k,placed,segment,
    stock_lower_resolved_source_record_form_coverage run scope events records source original⟩

end Backend.Stock.Proof.Coverage.Result
