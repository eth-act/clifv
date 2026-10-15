import FV.Backend.Proof.StockDivSignedSelected
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Every actual retained signed division record supplies its real result
binding and internally derived general/safe selected path under original scope. -/
theorem stock_lower_sdiv_record_receipt {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord} {step : Step} {info : IInfo}
    {ty : Clif.Ty} {x y : Nat}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.div .sdiv ty x y))
    (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ receipt : RecordSelection event record step,
      SignedSelectedReceipt event.ctx x y ty.width (scanState record.input record.inst) receipt.next receipt.out := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  exact ⟨receipt,stock_div_sdiv_selected (stock_lower_record_context run scope events).1 source clif receipt.selected⟩
end Backend.Stock.Proof.ScalarDiv
