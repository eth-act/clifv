import FV.Backend.Proof.StockDivSelected
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- A retained record of the actual successful driver supplies result binding
and its complete selected unsigned division receipt internally. -/
theorem stock_lower_udiv_record_receipt {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord} {step : Step} {info : IInfo}
    {ty : Clif.Ty} {x y : Nat}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.div .udiv ty x y))
    (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ receipt : RecordSelection event record step,
      if ty.width = 64 then WideUdivReceipt program event.ctx 999949 x y
        (scanState record.input record.inst) receipt.next #[] receipt.out
      else NarrowUdivReceipt program event.ctx 999949 x y ty.width
        (scanState record.input record.inst) receipt.next #[] receipt.out := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  exact ⟨receipt,stock_div_udiv_selected (stock_lower_record_context run scope events).1 source clif receipt.selected⟩
/-- Both signed/unsigned retained remainder records supply real result binding
and selected divide/multiply-subtract receipts without external helper certificates. -/
theorem stock_lower_rem_record_receipt {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (signed : Bool)
    {event : BlockScanEvent} {record : ScanRecord} {step : Step} {info : IInfo}
    {ty : Clif.Ty} {x y : Nat}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.div (if signed then .srem else .urem) ty x y))
    (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∃ receipt : RecordSelection event record step,
      if ty.width = 64 then WideRemReceipt program event.ctx signed 999899 x y
        (scanState record.input record.inst) receipt.next #[] receipt.out
      else NarrowRemReceipt program event.ctx signed 999899 x y ty.width
        (scanState record.input record.inst) receipt.next #[] receipt.out := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  exact ⟨receipt,stock_div_rem_selected (stock_lower_record_context run scope events).1 signed source clif receipt.selected⟩
end Backend.Stock.Proof.ScalarDiv
